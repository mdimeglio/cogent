--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

module Cogent.Common.Repr where

import Cogent.Common.Syntax
import qualified Cogent.Surface as S
import Cogent.Util (mapAccumLM)

import Control.Arrow ((&&&))
import qualified Data.Map as M
import Text.Parsec.Pos

data RepData = Rep
               { originalDecl :: S.RepDecl
               , name :: RepName
               , representation :: Representation
               }

-- vvv NOTE: The offsets in the datatype are relative to the top-level data structure,
-- instead of its parent. This means some calculation might be required when we recurse on
-- data representations. / zilinc
data Representation = Bits    { allocSize    :: Int
                              , allocOffset  :: Int }  -- in bits 
                    | Record  { fields       :: M.Map FieldName Representation }
                    | Variant { tagSize      :: Int
                              , tagOffset    :: Int
                              , alternatives :: M.Map TagName (Integer, Representation) }
                    deriving (Show, Eq, Ord)

data InternalRepr   = IWord     Int  -- word-size(in byte)
                    | IStruct [(FieldName, InternalField)]
                    | IChunk    Int  -- #bytes

data InternalField  = IField      InternalRepr
                    | IFieldGroup [(FieldName, Int)]  -- #bits(<8); a group is of 1 byte in total
                    | IUnion      [(TagName, InternalRepr)]

{- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- [NOTE: Relevant C optimisations]

-- This information is from: https://gcc.gnu.org/onlinedocs/gcc-6.3.0/gcc/Optimize-Options.html#Optimize-Options

" -fstrict-aliasing
" Allow the compiler to assume the strictest aliasing rules applicable to the
" language being compiled. For C (and C++), this activates optimizations based
" on the type of expressions. In particular, an object of one type is assumed
" never to reside at the same address as an object of a different type, unless
" the types are almost the same. For example, an unsigned int can alias an int,
" but not a void* or a double. A character type may alias any other type.
" Pay special attention to code like this:
" 
"           union a_union {
"             int i;
"             double d;
"           };
"           
"           int f() {
"             union a_union t;
"             t.d = 3.0;
"             return t.i;
"           }
" The practice of reading from a different union member than the one most
" recently written to (called “type-punning”) is common. Even with -fstrict-aliasing,
" type-punning is allowed, provided the memory is accessed through the union type.
" So, the code above works as expected. See Structures unions enumerations and
" bit-fields implementation[link]. However, this code might not:
" 
"           int f() {
"             union a_union t;
"             int* ip;
"             t.d = 3.0;
"             ip = &t.i;
"             return *ip;
"           }
" Similarly, access by taking the address, casting the resulting pointer and
" dereferencing the result has undefined behavior, even if the cast uses a
" union type, e.g.:
" 
"           int f() {
"             double d = 3.0;
"             return ((union a_union *) &d)->i;
"           }
" The -fstrict-aliasing option is enabled at levels -O2, -O3, -Os. 

For this reason, we might want to generate more distinct types for different
representations so that gcc can optimise better.

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ --}

{- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- [NOTE: C attributes relating to layout]

Common gcc attributes include `aligned' and `packed'.
See more here: https://gcc.gnu.org/onlinedocs/gcc-3.3/gcc/Type-Attributes.html
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ --}

sizeBits :: Representation -> Int
sizeBits (Bits sz off) = sz + off
sizeBits (Record fs) = maximum $ map sizeBits $ M.elems fs
sizeBits (Variant tsz toff alts) = maximum $ tsz + toff : map (sizeBits . snd) (M.elems alts)

sizeBytes :: Representation -> Int
sizeBytes r = let (d,m) = sizeBits r `divMod` 8
                in if m == 0 then d else d + 1

offsetBits :: Representation -> Int
offsetBits (Bits _ off) = off
offsetBits (Record fs) = minimum $ map offsetBits $ M.elems fs
offsetBits (Variant tsz toff alts) = minimum $ toff : map (offsetBits . snd) (M.elems alts)

offsetBytes :: Representation -> Int
offsetBytes r = let (d,m) = offsetBits r `divMod` 8
                 in if m == 0 then d else d + 1

byteAligned :: Representation -> Bool
byteAligned (Bits sz off)
  | sz `mod` 8 == 0 && off `mod` 8 == 0 = True
  | otherwise = False
byteAligned (Record fs) = and $ map byteAligned $ M.elems fs
byteAligned (Variant tsz toff alts)
  | tsz `mod` 8 == 0 && toff `mod` 8 == 0 &&
    and (map (byteAligned . snd) $ M.elems alts) = True
  | otherwise = False

isBitfield :: Representation -> Bool
isBitfield (Bits sz off) | sz `mod` 8 /= 0 && off `mod` 8 == 0 = True
isBitfield _ = False

-- restructure a repr so that it's more easily representable by C datatypes
restructure :: Representation -> InternalRepr
-- restructure r@(Record fs) 
--   | not $ byteAligned r = let (gs,hs) = spilt byteAligned fs
--                               (offs, szs) = map (sizeBits &&& offsetBits) hs
--                               
-- restructure r@(Variant tsz toff alts) = undefined
restructure r = undefined

-- group fields that are not byte-aligned into fields that are byte-aligned
-- ASSUME: all input reprs are byte-UNaligned
-- group :: [Representation] -> [Representation]
-- group [] = []
-- group [x] = __impossible "group: can't turn one unaliged field to an aligned field"
-- group xs = undefined

-- Once we have repr in the surface lang, this can be removed.
dummyRepr = Bits 0 0

type Allocation = [[Block]] -- disjunction of conjunctions

data Block = Block { blockSize :: Int, blockOffset :: Int, blockContext :: RepContext }
           deriving (Eq, Show, Ord)

data RepContext = InField FieldName SourcePos RepContext
                | InTag RepContext
                | InAlt TagName SourcePos RepContext
                | InDecl S.RepDecl
                deriving (Eq, Show, Ord)

data RepError = OverlappingBlocks Block Block
              | UnknownRepr RepName RepContext
              | TagMustBeSingleBlock RepContext
              deriving (Eq, Show, Ord)

(\/) :: Allocation -> Allocation -> Either RepError Allocation 
a \/ b = Right (a ++ b)

(/\) :: Allocation -> Allocation -> Either RepError Allocation
(x:xs) /\ b = (++) <$> helper x b <*> (xs /\ b)
  where helper :: [Block] -> [[Block]] -> Either RepError Allocation
        helper bs (y:ys) = let os = [(b1,b2) | b1 <- bs, b2 <- y, overlaps b1 b2]
                            in case os of 
                                [] -> ((bs ++ y):) <$> helper bs ys 
                                (b1,b2):_ -> Left $ OverlappingBlocks b1 b2
        helper bs [] = Right []

        overlaps (Block s1 o1 _) (Block s2 o2 _) = o1 >= o2 && o1 < (o2 + s2)
                                                || o2 >= o1 && o2 < (o1 + s1)
[] /\ b = pure b


offsetAllocation :: Int -> Allocation -> Allocation 
offsetAllocation off = map (map (\(Block s o c) -> Block s (o + off) c))

offsetRep :: Int -> Representation -> Representation
offsetRep off (Bits s o) = Bits s (o + off)
offsetRep off (Variant s o vs) = Variant s (o + off) (fmap (fmap (offsetRep off)) vs)
offsetRep off (Record fs) = Record (fmap (offsetRep off) fs)

compile :: M.Map RepName (Allocation, RepData) -> S.RepDecl -> Either RepError (Allocation, RepData)
compile env d@(S.RepDecl p n a) = fmap (Rep d n) <$> evalAlloc (InDecl d) a
  where evalSize (S.Bytes b) = b * 8
        evalSize (S.Bits b) = b
        evalSize (S.Add a b) = evalSize a + evalSize b

        evalAlloc ctx (S.RepRef n) = do 
            case M.lookup n env of 
                Just (a,Rep _ _ r) -> Right (a,r)
                Nothing    -> Left $ UnknownRepr n ctx
        evalAlloc ctx (S.Prim s) = Right ([[Block (evalSize s) 0 ctx]], Bits (evalSize s) 0)
        evalAlloc ctx (S.Offset e off) = do
            (a', r') <- evalAlloc ctx e
            return (offsetAllocation (evalSize off) a', offsetRep (evalSize off) r')
        evalAlloc ctx (S.Record fs) = do
            let step alloc (f,pos,r) = do
                  (a, r') <- evalAlloc (InField f pos ctx) r 
                  a' <- a /\ alloc 
                  return (a', (f, r'))
            (a, fs') <- mapAccumLM step [[]] fs 
            pure (a, Record $ M.fromList fs')
        evalAlloc ctx (S.Variant e vs) = do
            (a, td) <- evalAlloc (InTag ctx) e
            case a of 
                [[Block ts to _]] -> do
                    let step alloc (f,pos,i,r) = do 
                            (a, r') <- evalAlloc (InAlt f pos ctx) r
                            a' <- a \/ alloc
                            return (a', (f,(i,r')))
                    (a', vs') <- mapAccumLM step a vs
                    pure (a', Variant ts to $ M.fromList vs')
                _ -> Left $ TagMustBeSingleBlock (InTag ctx)


