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

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Cogent.TypeCheck.Generator
  ( runCG
  , CG
  , cg
  , cgFunDef
  , freshTVar
  , validateType
  ) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Context as C
import Cogent.PrettyPrint (prettyC)
import Cogent.Surface
import Cogent.TypeCheck.Base hiding (validateType)
import Cogent.TypeCheck.Util
import Cogent.Util hiding (Warning)

import Control.Arrow (first, second)
import Control.Lens hiding (Context, each, zoom, (:<))
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Functor.Compose
import Data.List (nub, (\\))
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Maybe (catMaybes, isNothing, isJust)
import Data.Monoid ((<>))
import qualified Data.Sequence as Seq
import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen hiding ((<>), (<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as L

-- import Debug.Trace

data GenState = GenState { _context :: C.Context TCType
                         , _knownTypeVars :: [TyVarName]
                         , _flexes :: Int
                         , _flexOrigins :: IM.IntMap VarOrigin
                         }

makeLenses ''GenState

type CG a = TcConsM GenState a

runCG :: C.Context TCType -> [TyVarName] -> CG a -> TcM (a, Int, IM.IntMap VarOrigin)
runCG g vs ma = do
  (a, GenState _ _ f os) <- withTcConsM (GenState g vs 0 mempty) ((,) <$> ma <*> get)
  return (a,f,os)


-- -----------------------------------------------------------------------------
-- Type-level constraints
-- -----------------------------------------------------------------------------

validateType :: RawType -> CG (Constraint, TCType)
validateType rt@(RT t) = do
  vs <- use knownTypeVars
  ts <- lift $ use knownTypes
  case t of
    TVar v _ | v `notElem` vs -> return (Unsat $ UnknownTypeVariable v, toTCType rt)
    TCon t as _ | Nothing <- lookup t ts -> return (Unsat $ UnknownTypeConstructor t, toTCType rt)
                | Just (vs, _) <- lookup t ts
                , provided <- length as
                , required <- length vs
                , provided /= required
               -> return (Unsat $ TypeArgumentMismatch t provided required, toTCType rt)
    TRecord fs _ | fields  <- map fst fs
                 , fields' <- nub fields
                -> if fields' == fields
                   then second (T . ffmap toSExpr) <$> fmapFoldM validateType t
                   else return (Unsat $ DuplicateRecordFields (fields \\ fields'), toTCType rt)
    TArray te l -> do let l' = toSExpr l
                          cl = ForAll (SE (PrimOp ">" [l', SE (IntLit 0) (T t_u32)]) (T t_bool))
                      (c,te') <- validateType te
                      return (c <> cl, T $ TArray te' l')
    TRefine v t e -> do let t' = toTCType t
                        context %= C.addScope (M.singleton v (t', noPos, Seq.singleton noPos))
                        (c,e') <- cg (dummyLocE e) (T $ TCon "Bool" [] Unboxed)
                        return (c, T $ TRefine v t' $ tcToSExpr e')
    _ -> second (T . ffmap toSExpr) <$> fmapFoldM validateType t 

validateTypes :: (Traversable t) => t RawType -> CG (Constraint, t TCType)
validateTypes ts = fmapFoldM validateType ts

-- -----------------------------------------------------------------------------
-- Term-level constraints
-- -----------------------------------------------------------------------------

cgFunDef :: (?loc :: SourcePos) => [Alt LocPatn LocExpr] -> TCType -> CG (Constraint, [Alt TCPatn TCExpr])
cgFunDef alts t = do
  alpha1 <- freshTVar
  alpha2 <- freshTVar
  traceTc "gen" (text "function is given type" <> colon
                 <+> pretty alpha1 <+> text "->" <+> pretty alpha2) 
  (c, alts') <- cgAlts alts alpha2 alpha1
  return (c <> (F $ T (TFun alpha1 alpha2)) :< F t, alts')

-- TODO: When we encounter a pattern match, we take the union of the smallest type
-- each pattern can represent. The sum will be used to compare with upper level types.
-- E.g. x | False -> e1; | True -> e2
-- PBool False : {b : Bool | b == False} == tt
-- PBool True  : {b : Bool | b == True } == ff
-- if x : ?0
-- then ?0 :< tt `union` ff

-- cgAlts alts out_type in_type
-- NOTE the order of arguments!
cgAlts :: [Alt LocPatn LocExpr] -> TCType -> TCType -> CG (Constraint, [Alt TCPatn TCExpr])
cgAlts alts top alpha = do
  let
    altPattern (Alt p _ _) = p

    f (Alt p l e) t = do
      (s, c, p') <- matchA p t
      context %= C.addScope s
      (c', e') <- cg e top
      rs <- context %%= C.dropScope
      let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) ->
            case us of Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v); _ -> Sat
      return (removeCase p t, (c <> c' <> dropConstraintFor rs <> unused, Alt p' l e'))

    jobs = map (\(n, alt) -> (NthAlternative n (altPattern alt), f alt)) (zip [1..] alts)

  (c'', blob) <- parallel jobs alpha

  let (cs, alts') = unzip blob
      c = mconcat (Exhaustive alpha (map (toRawPatn . altPattern) $ toTypedAlts alts'):c'':cs)
  return (c, alts')


-- -----------------------------------------------------------------------------
-- Expression constraints
-- -----------------------------------------------------------------------------

cgMany :: (?loc :: SourcePos) => [LocExpr] -> CG ([TCType], Constraint, [TCExpr])
cgMany es = do
  let each (ts,c,es') e = do
        alpha    <- freshTVar
        (c', e') <- cg e alpha
        return (alpha:ts, c <> c', e':es')
  (ts, c', es') <- foldM each ([], Sat, []) es  -- foldM is the same as foldlM
  return (reverse ts, c', reverse es')

cg :: LocExpr -> TCType -> CG (Constraint, TCExpr)
cg x@(LocExpr l e) t = do
  let ?loc = l
  (c, e') <- cg' e t
  return (c :@ InExpression x t, TE t e' l)

cg' :: (?loc :: SourcePos)
    => Expr LocType LocPatn LocIrrefPatn LocExpr
    -> TCType
    -> CG (Constraint, Expr TCType TCPatn TCIrrefPatn TCExpr)
-- TODO: generate refinement constraints for prim-ops
cg' (PrimOp o [e1, e2]) t
  | o `elem` words "+ - * / % .&. .|. .^. >> <<"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (integral t <> c1 <> c2, PrimOp o [e1', e2'])
  | o `elem` words "&& ||"
  = do (c1, e1') <- cg e1 t
       (c2, e2') <- cg e2 t
       return (F (T (TCon "Bool" [] Unboxed)) :< F t <> c1 <> c2, PrimOp o [e1', e2'])
  | o `elem` words "== /= >= <= > <"
  = do alpha <- freshTVar
       (c1, e1') <- cg e1 alpha
       (c2, e2') <- cg e2 alpha
       let c  = F (T (TCon "Bool" [] Unboxed)) :< F t
           c' = integral alpha
       return (c <> c' <> c1 <> c2, PrimOp o [e1', e2'])
cg' (PrimOp o [e]) t
  | o == "complement"  = do
      (c, e') <- cg e t
      return (integral t :& c, PrimOp o [e'])
  | o == "not"         = do
      (c, e') <- cg e t
      return (F (T (TCon "Bool" [] Unboxed)) :< F t :& c, PrimOp o [e'])
cg' (PrimOp _ _) _ = __impossible "cg': unimplemented primops"
cg' (Var n) t = do
  let e = Var n  -- it has a different type than the above `Var n' pattern
  ctx <- use context
  traceTc "gen" (text "cg for variable" <+> pretty n L.<$> text "of type" <+> pretty t)
  case C.lookup n ctx of
    -- Variable not found, see if the user meant a function.
    Nothing ->
      lift (use $ knownFuns.at n) >>= \case
        Just _  -> cg' (TypeApp n [] NoInline) t
        Nothing -> return (Unsat (NotInScope (funcOrVar t) n), e)

    -- Variable used for the first time, mark the use, and continue
    Just (t', _, Seq.Empty) -> do
      context %= C.use n ?loc
      let c = F t' :< F t
      traceTc "gen" (text "variable" <+> pretty n <+> text "used for the first time" <> semi
               L.<$> text "generate constraint" <+> prettyC c)
      return (c, e)

    -- Variable already used before, emit a Share constraint.
    Just (t', p, us)  -> do
      context %= C.use n ?loc
      traceTc "gen" (text "variable" <+> pretty n <+> text "used before" <> semi
               L.<$> text "generate constraint" <+> prettyC (F t' :< F t) <+> text "and share constraint")
      return (Share t' (Reused n p us) <> F t' :< F t, e)

cg' (Upcast e) t = do
  alpha <- freshTVar
  (c1, e1') <- cg e alpha
  let c = (integral alpha) <> Upcastable alpha t <> c1
  return (c, Upcast e1')


-- TODO: What type should be infer for primitive types?
-- It seems that we should generate the most specific types
-- but it will incur extensive subtyping relations in the
-- syntax tree. / zilinc
cg' (BoolLit b) t = do
  v@(SU i _) <- freshEVar (T t_bool)
  let r = SAll i $ SE (PrimOp "==" [v, SE (BoolLit b) (T t_bool)]) (T t_bool)
      c = F (T (TRefine (unknownName v) (T t_bool) r)) :< F t
      e = BoolLit b
  return (c,e)

cg' (CharLit l) t = do
  let c = F (T (TCon "U8" [] Unboxed)) :< F t
      e = CharLit l
  return (c,e)

cg' (StringLit l) t = do
  let c = F (T (TCon "String" [] Unboxed)) :< F t
      e = StringLit l
  return (c,e)

cg' Unitel t = do
  let c = F (T TUnit) :< F t
      e = Unitel
  return (c,e)

cg' (IntLit n) t = do
  let minimumBitwidth | n < u8MAX      = "U8"
                      | n < u16MAX     = "U16"
                      | n < u32MAX     = "U32"
                      | otherwise      = "U64"
  let bt = TCon minimumBitwidth [] Unboxed
  t' <- freshTVar
  v@(SU i _) <- freshEVar t'
  let r = SAll i $ SE (PrimOp "==" [v, SE (IntLit n) t']) (T t_bool)
      -- NOTE: We need a 2-step promition scheme here. E.g.:
      -- (1) U8 :~> U32  (upcast)
      -- (2) {v : U32 | P'(v)} :<  {v : U32 | Q (v)}  (ref. subtyping)
      c = Upcastable (T bt) t :& (F $ T $ TRefine (unknownName v) t' r) :< F t
      e = IntLit n
  return (c,e)

cg' (ArrayLit es) t = do
  alpha <- freshTVar
  blob <- forM es $ flip cg alpha
  let (cs,es') = unzip blob
      n = SE (IntLit . fromIntegral $ length es) (T t_u32)
      cz = ForAll (SE (PrimOp ">" [n, SE (IntLit 0) (T t_u32)]) (T t_bool))
  return (mconcat cs <> cz <> F (T $ TArray alpha n) :< F t, ArrayLit es')

cg' (ArrayIndex e i) t = do
  alpha <- freshTVar
  n <- freshEVar (T t_u32)
  let ta = T $ TArray alpha n
  (ce, e') <- cg e ta
  (ci, i') <- cg (dummyLocE i) (T t_u32)
  let c = F alpha :< F t <> Share ta UsedInArrayIndexing
        <> ForAll (SE (PrimOp "<" [toSExpr i, n]) (T t_bool))
        -- <> ForAll (SE (PrimOp ">=" [toSExpr i, SE (IntLit 0)]))  -- as we don't have negative values
  return (ce <> ci <> c, ArrayIndex e' i)

cg' exp@(Lam pat mt e) t = do
  alpha <- freshTVar
  beta  <- freshTVar
  (ct, alpha') <- case mt of
    Nothing -> return (Sat, alpha)
    Just t' -> do
      tvs <- use knownTypeVars
      lift (runExceptT $ validateType' tvs (stripLocT t')) >>= \case
        Left  e   -> return (Unsat e, alpha)
        Right t'' -> return (F alpha :< F t'', t'')
  (s, cp, pat') <- match pat alpha'
  let fvs = fvE $ stripLocE (LocExpr noPos $ Lam pat mt e)
  ctx <- use context
  let fvs' = filter (C.contains ctx) fvs  -- including (bad) vars that are not in scope
  context %= C.addScope s
  (ce, e') <- cg e beta
  rs <- context %%= C.dropScope
  let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) -> 
        case us of
          Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v)
          _ -> Sat
      c = ct <> cp <> ce <> F (T $ TFun alpha beta) :< F t
             <> dropConstraintFor rs <> unused
      lam = Lam  pat' (fmap (const alpha) mt) e'
  unless (null fvs') $ __todo "closures not implemented"
  unless (null fvs') $ context .= ctx
  traceTc "gen" (text "lambda expression" <+> prettyE lam
           L.<$> text "generate constraint" <+> prettyC c <> semi)
  return (c,lam)

cg' (App e1 e2 _) t = do
  alpha     <- freshTVar
  (c1, e1') <- cg e1 (T (TFun alpha t))
  (c2, e2') <- cg e2 alpha

  let c = c1 <> c2
      e = App e1' e2' False
  traceTc "gen" (text "cg for funapp:" <+> prettyE e)
  return (c,e)

cg' (Comp f g) t = do
  alpha1 <- freshTVar
  alpha2 <- freshTVar
  alpha3 <- freshTVar
  
  (c1, f') <- cg f (T (TFun alpha2 alpha3))
  (c2, g') <- cg g (T (TFun alpha1 alpha2))
  let e = Comp f' g'
      c = c1 <> c2 <> F (T $ TFun alpha1 alpha3) :< F t
  traceTc "gen" (text "cg for comp:" <+> prettyE e)
  return (c,e)

cg' (Con k es) t = do
  (ts, c', es') <- cgMany es

  let e = Con k es'
      c = FVariant (M.fromList [(k, (ts, False))]) :< F t
  traceTc "gen" (text "cg for constructor:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)

cg' (Tuple es) t = do
  (ts, c', es') <- cgMany es

  let e = Tuple es'
      c = F (T (TTuple ts)) :< F t
  traceTc "gen" (text "cg for tuple:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)

cg' (UnboxedRecord fes) t = do
  let (fs, es) = unzip fes
  (ts, c', es') <- cgMany es

  let e = UnboxedRecord (zip fs es')
      r = T (TRecord (zip fs (map (, False) ts)) Unboxed)
      c = F r :< F t
  traceTc "gen" (text "cg for unboxed record:" <+> prettyE e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, e)

cg' (Seq e1 e2) t = do
  alpha <- freshTVar
  (c1, e1') <- cg e1 alpha
  (c2, e2') <- cg e2 t

  let e = Seq e1' e2'
      c = c1 <> Drop alpha Suppressed <> c2
  return (c, e)

cg' (TypeApp f as i) t = do
  tvs <- use knownTypeVars
  (ct, getCompose -> as') <- validateTypes (fmap stripLocT $ Compose as) 
  lift (use $ knownFuns.at f) >>= \case
    Just (PT vs tau) -> let
        match :: [(TyVarName, Kind)] -> [Maybe TCType] -> CG ([(TyVarName, TCType)], Constraint)
        match [] []    = return ([], Sat)
        match [] (_:_) = return ([], Unsat (TooManyTypeArguments f (PT vs tau)))
        match vs []    = freshTVar >>= match vs . return . Just
        match (v:vs) (Nothing:as) = freshTVar >>= \a -> match (v:vs) (Just a:as)
        match ((v,k):vs) (Just a:as) = do
          (ts, c) <- match vs as
          return ((v,a):ts, kindToConstraint k a (TypeParam f v) <> c)
      in do
        (ts,c') <- match vs as'

        let c = F (substType ts tau) :< F t
            e = TypeApp f (map (Just . snd) ts) i
        traceTc "gen" (text "cg for typeapp:" <+> prettyE e
                 L.<$> text "of type" <+> pretty t <> semi
                 L.<$> text "type signature is" <+> pretty (PT vs tau) <> semi
                 L.<$> text "generate constraint" <+> prettyC c)
        return (ct <> c' <> c, e)

    Nothing -> do
      let e = TypeApp f as' i
          c = Unsat (FunctionNotFound f)
      return (ct <> c, e)

cg' (Member e f) t = do
  alpha <- freshTVar
  (c', e') <- cg e alpha

  let f' = Member e' f
      x = FRecord [(f, (t, False))]
      c = F alpha :< x <> Share alpha (UsedInMember f)
  traceTc "gen" (text "cg for member:" <+> prettyE f'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (c' <> c, f')

cg' (If e1 bs e2 e3) t = do
  (c1, e1') <- letBang bs (cg e1) (T (TCon "Bool" [] Unboxed))
  (c, [(c2, e2'), (c3, e3')]) <- parallel' [(ThenBranch, cg e2 t), (ElseBranch, cg e3 t)]
  let e = If e1' bs e2' e3'
  traceTc "gen" (text "cg for if:" <+> prettyE e)
  return (c1 <> c <> c2 <> c3, e)

cg' (Put e ls) t | not (any isNothing ls) = do
  alpha <- freshTVar
  let (fs, es) = unzip (catMaybes ls)
  (c', e') <- cg e alpha
  (ts, cs, es') <- cgMany es

  let c1 = F (T (TPut (Just fs) alpha)) :< F t
      c2 = F alpha :< FRecord (zip fs (map (,True) ts))
      r = Put e' (map Just (zip fs es'))
  traceTc "gen" (text "cg for put:" <+> prettyE r
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint:" <+> prettyC c1 <+> text "and" <+> prettyC c2)
  return (c1 <> c' <> cs <> c2, r)

  | otherwise = first (<> Unsat RecordWildcardsNotSupported) <$> cg' (Put e (filter isJust ls)) t

cg' (Let bs e) t = do
  (c, bs', e') <- withBindings bs e t
  return (c, Let bs' e')

cg' (Match e bs alts) t = do
  alpha <- freshTVar
  (c', e') <- letBang bs (cg e) alpha
  (c'', alts') <- cgAlts alts t alpha

  let c = c' :& c''
      e'' = Match e' bs alts'
  return (c, e'')

cg' (Annot e tau) t = do
  tvs <- use knownTypeVars
  let t' = stripLocT tau
  (c, t'') <- lift (runExceptT $ validateType' tvs t') >>= \case
    Left  e'' -> return (Unsat e'', t)
    Right t'' -> return (F t :< F t'', t'')
  (c', e') <- cg e t''
  return (c <> c', Annot e' t'')


-- -----------------------------------------------------------------------------
-- Pattern constraints
-- -----------------------------------------------------------------------------

matchA :: LocPatn -> TCType -> CG (M.Map VarName (C.Row TCType), Constraint, TCPatn)
matchA x@(LocPatn l p) t = do
  let ?loc = l
  (s,c,p') <- matchA' p t
  return (s, c :@ InPattern x, TP p' l)

matchA' :: (?loc :: SourcePos)
       => Pattern LocIrrefPatn -> TCType
       -> CG (M.Map VarName (C.Row TCType), Constraint, Pattern TCIrrefPatn)

matchA' (PIrrefutable i) t = do
  (s, c, i') <- match i t
  return (s, c, PIrrefutable i')

matchA' (PCon k is) t = do
  (vs, blob) <- unzip <$> forM is (\i -> do alpha <- freshTVar; (alpha,) <$> match i alpha)
  let (ss, cs, is') = (map fst3 blob, map snd3 blob, map thd3 blob)
      p' = PCon k is'
      co = case overlapping ss of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
      c = F t :< FVariant (M.fromList [(k, (vs, False))]) 
  traceTc "gen" (text "match constructor pattern:" <+> pretty p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (M.unions ss, co <> mconcat cs <> c, p')

matchA' (PIntLit i) t = do
  let minimumBitwidth | i < u8MAX      = "U8"
                      | i < u16MAX     = "U16"
                      | i < u32MAX     = "U32"
                      | otherwise      = "U64"
      c = Upcastable (T (TCon minimumBitwidth [] Unboxed)) t
      -- ^^^ FIXME: I think if we restrict this constraint, then we can possibly get rid of `Upcast' / zilinc
  return (M.empty, c, PIntLit i)

matchA' (PBoolLit b) t =
  return (M.empty, F t :< F (T (TCon "Bool" [] Unboxed)), PBoolLit b)

matchA' (PCharLit c) t =
  return (M.empty, F t :< F (T (TCon "U8" [] Unboxed)), PCharLit c)

match :: LocIrrefPatn -> TCType -> CG (M.Map VarName (C.Row TCType), Constraint, TCIrrefPatn)
match x@(LocIrrefPatn l ip) t = do
  let ?loc = l
  (s,c,ip') <- match' ip t
  return (s, c :@ InIrrefutablePattern x, TIP ip' l)

match' :: (?loc :: SourcePos)
      => IrrefutablePattern VarName LocIrrefPatn -> TCType
      -> CG (M.Map VarName (C.Row TCType), Constraint, IrrefutablePattern TCName TCIrrefPatn)

match' (PVar x) t = do
  let p = PVar (x,t)
  traceTc "gen" (text "match var pattern:" <+> prettyIP p
           L.<$> text "of type" <+> pretty t)
  return (M.fromList [(x, (t,?loc,Seq.empty))], Sat, p)

match' (PUnderscore) t = 
  let c = dropConstraintFor (M.singleton "_" (t, ?loc, Seq.empty))
   in return (M.empty, c, PUnderscore)

match' (PUnitel) t = return (M.empty, F t :< F (T TUnit), PUnitel)

match' (PTuple ps) t = do
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p v) ps
  let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
      p' = PTuple ps'
      co = case overlapping ss of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
      c = F t :< F (T (TTuple vs))
  traceTc "gen" (text "match tuple pattern:" <+> prettyIP p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c)
  return (M.unions ss, co <> mconcat cs <> c, p')

match' (PUnboxedRecord fs) t | not (any isNothing fs) = do
  let (ns, ps) = unzip (catMaybes fs)
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p v) ps
  let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
      t' = FRecord (zip ns (map (,False) vs))
      d  = Drop (T (TTake (Just ns) t)) Suppressed
      p' = PUnboxedRecord (map Just (zip ns ps'))
      c = F t :< t'
      co = case overlapping ss of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
  traceTc "gen" (text "match unboxed record:" <+> prettyIP p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c
           L.<$> text "non-overlapping, and linearity constraints")
  return (M.unions ss, co <> mconcat cs <> c <> d, p')

  | otherwise = second3 (:& Unsat RecordWildcardsNotSupported) <$> match' (PUnboxedRecord (filter isJust fs)) t

match' (PTake r fs) t | not (any isNothing fs) = do
  let (ns, ps) = unzip (catMaybes fs)
  (vs, blob) <- unzip <$> mapM (\p -> do v <- freshTVar; (v,) <$> match p v) ps
  let (ss, cs, ps') = (map fst3 blob, map snd3 blob, map thd3 blob)
      s  = M.fromList [(r, (u, ?loc, Seq.empty))]
      u  = T (TTake (Just ns) t)
      c  = F t :< FRecord (zip ns (map (,False) vs))
      p' = PTake (r,u) (map Just (zip ns ps'))
      co = case overlapping (s:ss) of
             Left (v:_) -> Unsat $ DuplicateVariableInPattern v  -- p'
             _          -> Sat
  traceTc "gen" (text "match take pattern:" <+> pretty p'
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint:" <+> prettyC c
           L.<$> text "and non-overlapping constraints")
  return (M.unions (s:ss), co <> mconcat cs <> c, p')

  | otherwise = second3 (:& Unsat RecordWildcardsNotSupported) <$> match' (PTake r (filter isJust fs)) t

match' (PArray ps) t = do
  alpha <- freshTVar
  blob <- mapM (flip match alpha) ps
  let (ss,cs,ps') = unzip3 blob
      l = SE (IntLit . fromIntegral $ length ps) (T t_u32)
      c = F t :< F (T $ TArray alpha l)
  return (M.unions ss, mconcat cs <> c, PArray ps')


-- -----------------------------------------------------------------------------
-- Auxiliaries
-- -----------------------------------------------------------------------------

freshTVar :: (?loc :: SourcePos) => CG TCType
freshTVar = fresh (ExpressionAt ?loc)
  where
    fresh :: VarOrigin -> CG TCType
    fresh ctx = do
      i <- flexes <<%= succ
      flexOrigins %= IM.insert i ctx
      return $ U i

freshEVar :: (?loc :: SourcePos) => TCType -> CG SExpr
freshEVar t = fresh (ExpressionAt ?loc)
  where
    fresh :: VarOrigin -> CG SExpr
    fresh ctx = do
      i <- flexes <<%= succ  -- FIXME: do we need a different counter?
      flexOrigins %= IM.insert i ctx
      return $ SU i t
      
integral :: TCType -> Constraint
integral a = Upcastable (T (TCon "U8" [] Unboxed)) a

dropConstraintFor :: M.Map VarName (C.Row TCType) -> Constraint
dropConstraintFor m = foldMap (\(i, (t,x,us)) -> if null us then Drop t (Unused i x) else Sat) $ M.toList m

parallel' :: [(ErrorContext, CG (Constraint, a))] -> CG (Constraint, [(Constraint, a)])
parallel' ls = parallel (map (second (\a _ -> ((),) <$> a)) ls) ()

parallel :: [(ErrorContext, acc -> CG (acc, (Constraint, a)))]
         -> acc
         -> CG (Constraint, [(Constraint, a)])
parallel []       _   = return (Sat, [])
parallel [(ct,f)] acc = (Sat,) . return . first (:@ ct) . snd <$> f acc
parallel ((ct,f):xs) acc = do
  ctx  <- use context
  (acc', x) <- second (first (:@ ct)) <$> f acc
  ctx1 <- use context
  context .= ctx
  (c', xs') <- parallel xs acc'
  ctx2 <- use context
  let (ctx', ls, rs) = C.merge ctx1 ctx2
  context .= ctx'
  let cls = foldMap (\(n, (t, p, us@(_ Seq.:<| _))) -> Drop t (UnusedInOtherBranch n p us)) ls
      crs = foldMap (\(n, (t, p, us@(_ Seq.:<| _))) -> Drop t (UnusedInThisBranch  n p us)) rs
  return (c' <> ((cls <> crs) :@ ct), x:xs')



withBindings :: (?loc::SourcePos)
  => [Binding LocType LocPatn LocIrrefPatn LocExpr]
  -> LocExpr -- expression e to be checked with the bindings
  -> TCType  -- the type for e
  -> CG (Constraint, [Binding TCType TCPatn TCIrrefPatn TCExpr], TCExpr)
withBindings [] e top = do
  (c, e') <- cg e top
  return (c, [], e')
withBindings (Binding pat tau e0 bs : xs) e top = do
  alpha <- freshTVar
  (c0, e0') <- letBang bs (cg e0) alpha
  (ct, alpha') <- case tau of
    Nothing -> return (Sat, alpha)
    Just tau' -> do
      tvs <- use knownTypeVars
      lift (runExceptT $ validateType' tvs (stripLocT tau')) >>= \case
        Left  e -> return (Unsat e, alpha)
        Right t -> return (F alpha :< F t, t)
  (s, cp, pat') <- match pat alpha'
  context %= C.addScope s
  (c', xs', e') <- withBindings xs e top
  rs <- context %%= C.dropScope
  let unused = flip foldMap (M.toList rs) $ \(v,(_,_,us)) -> 
        case us of
          Seq.Empty -> warnToConstraint __cogent_wunused_local_binds (UnusedLocalBind v)
          _ -> Sat
      c = ct <> c0 <> c' <> cp <> dropConstraintFor rs <> unused
      b' = Binding pat' (fmap (const alpha) tau) e0' bs
  traceTc "gen" (text "bound expression" <+> pretty e0' <+> 
                 text "with banged" <+> pretty bs
           L.<$> text "of type" <+> pretty alpha <> semi
           L.<$> text "generate constraint" <+> prettyC c0 <> semi
           L.<$> text "constraint for ascribed type:" <+> prettyC ct)
  return (c, b':xs', e')
withBindings (BindingAlts pat tau e0 bs alts : xs) e top = do
  alpha <- freshTVar
  (c0, e0') <- letBang bs (cg e0) alpha
  (ct, alpha') <- case tau of
    Nothing -> return (Sat, alpha)
    Just tau' -> do
      tvs <- use knownTypeVars
      lift (runExceptT $ validateType' tvs (stripLocT tau')) >>= \case
        Left  e -> return (Unsat e, alpha)
        Right t -> return (F alpha :< F t, t)
  (calts, alts') <- cgAlts (Alt pat Regular (LocExpr (posOfE e) (Let xs e)) : alts) top alpha'
  let c = c0 <> ct <> calts
      (Alt pat' _ (TE _ (Let xs' e') _)) : altss' = alts'
      b0' = BindingAlts pat' (fmap (const alpha) tau) e0' bs altss'
  return (c, b0':xs', e')

letBang :: (?loc :: SourcePos) => [VarName] -> (TCType -> CG (Constraint, TCExpr)) -> TCType -> CG (Constraint, TCExpr)
letBang [] f t = f t
letBang bs f t = do
  c <- foldMap id <$> mapM validateVariable bs
  ctx <- use context
  let (ctx', undo) = C.mode ctx bs (\(t,p,_) -> (T (TBang t), p, Seq.singleton ?loc))  -- FIXME: shall we also take the old `us'?
  context .= ctx'
  (c', e) <- f t
  context %= undo  -- NOTE: this is NOT equiv. to `context .= ctx'
  let c'' = Escape t UsedInLetBang
  traceTc "gen" (text "let!" <+> pretty bs <+> text "when cg for expression" <+> pretty e
           L.<$> text "of type" <+> pretty t <> semi
           L.<$> text "generate constraint" <+> prettyC c'')
  return (c <> c' <> c'', e)

validateVariable :: VarName -> CG Constraint
validateVariable v = do
  x <- use context
  return $ if C.contains x v then Sat else Unsat (NotInScope MustVar v)


-- ----------------------------------------------------------------------------
-- pp for debugging
-- ----------------------------------------------------------------------------

prettyE :: Expr TCType TCPatn TCIrrefPatn TCExpr -> Doc
prettyE = pretty

-- prettyP :: Pattern TCIrrefPatn -> Doc
-- prettyP = pretty

prettyIP :: IrrefutablePattern TCName TCIrrefPatn -> Doc
prettyIP = pretty


