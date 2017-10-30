--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


module Cogent.HscSyntax where

import Prelude hiding ((<$>))
import Text.PrettyPrint.ANSI.Leijen as PP


-- NOTE: This syntax is meant to be kept simple, rather than complete. / zilinc


data HscModule = HscModule [ModulePragma] ModuleName [Declaration]

data ModulePragma = LanguagePragma String

data Declaration = HsDecl HsDecl | HscDecl HscDecl

data HsDecl = DataDecl TypeName [TyVarName] [DataCon]
            | TypeDecl TypeName [TyVarName] Type
            | InstDecl ClassName [Context] Type [Binding]

data Context = Context ClassName Type

data Binding = Binding VarName [Pattern] Expression

data Pattern = PVar VarName
             | PCon ConsName [Pattern]

data Expression = EVar VarName
                | EDo [DoStatement]
                | EOp OpName [Expression]
                | ECon ConsName [Expression]
                | EApp Expression [Expression]
                | EAbs [Pattern] Expression
                | ELet [Binding] Expression
                | EHsc HscSymbol Expression
                | ETuple [Expression]

data HscSymbol = HscPeek | HscPoke | HscSize | HscAlignment

data DoStatement = DoBind [Pattern] Expression
                 | DoLet  [Binding]

data DataCon = DataCon ConsName [(FieldName, Type)]


data Type = TyCon ConsName [Type]
          | TyVar TyVarName

data HscDecl = HashInclude String | HashEnum TypeName ConsName [TagName]

type ModuleName = String
type VarName    = String
type OpName     = String
type TyVarName  = String
type TypeName   = String
type ConsName   = String
type ClassName  = String
type FieldName  = String
type TagName    = String


-- *****************************************************************************
-- Pretty-printer
--

class Pretty t => Pretty' t where
  pretty' :: Int -> t -> Doc
  pretty' l x = if l > level x then parens (pretty x) else pretty x

  level :: t -> Int

instance Pretty HscModule where
  pretty (HscModule pragmas name decls) = prettyList pragmas
                                     <$$> text "module" <+> text name <+> text "where"
                                     <$$> empty
                                     <$$> prettyList decls

instance Pretty ModulePragma where
  pretty (LanguagePragma s) = text "{-# LANGUAGE" <+> text s <+> text "#-}"
  prettyList ps = vcat $ map pretty ps
 
instance Pretty Declaration where
  pretty (HsDecl  d) = pretty d
  pretty (HscDecl d) = pretty d
  
  prettyList ds = vsep $ map pretty ds

instance Pretty HsDecl where
  pretty (DataDecl tn tvs datacons) = undefined
  pretty (TypeDecl tn tvs ty) = text "type" <+> pretty tn <+> hsep (map pretty tvs) <+> text "=" <+> pretty ty
  pretty (InstDecl cl ctxs ty bindings) = text "instance" <+> prettyList ctxs <+> text "=>" <+> text cl <+> pretty ty <+> text "where"
                                     <$$> prettyList bindings

instance Pretty Context where
  pretty (Context cl ty) = text cl <+> pretty ty
  
  prettyList []  = empty
  prettyList [c] = pretty c
  prettyList cs  = tupled $ map pretty cs

instance Pretty Binding where
  pretty (Binding f ps e) = text f <+> prettyList ps <+> text "=" <+> pretty e
  prettyList bs = align $ vsep $ map pretty bs

instance Pretty Pattern where
  pretty (PVar v) = text v
  pretty (PCon cn ps) = text cn <+> prettyList ps

  prettyList ps  = hsep $ map pretty ps

-- Expression
instance Pretty Expression where
  pretty (EVar v) = text v
  pretty (EDo ds) = text "do"
               <$> align (prettyList ds)
  pretty (EOp o es) = parens (text o) <+> prettyList es
  pretty (ECon cn es) = text cn <+> prettyList es
  pretty (EApp f es) = pretty f <+> prettyList es
  pretty (EAbs ps e) = text "\\" <> prettyList ps <+> text "->" <+> pretty e
  pretty (ELet bs e) = text "let" <+> align (prettyList bs)
                   <$> text "in" <+> pretty e
  pretty (EHsc s e) = pretty s <+> pretty e
  pretty (ETuple es) = tupled $ map pretty es

  prettyList es = hsep $ map pretty es

instance Pretty HscSymbol where
  pretty HscPeek = text "#peek"
  pretty HscPoke = text "#poke"
  pretty HscSize = text "#size"
  pretty HscAlignment = text "#alignment"

instance Pretty DoStatement where
  pretty (DoBind ps e) = prettyList ps <+> text "<-" <+> pretty e
  pretty (DoLet bs) = prettyList bs

  prettyList ds = align $ vsep $ map pretty ds

instance Pretty DataCon where
  pretty (DataCon cn fts) = text cn <+> encloseSep lbrace rbrace comma (map (\(f,t) -> text f <+> text "::" <+> pretty t) fts)

instance Pretty Type where
  pretty (TyCon cn ts) = text cn <+> prettyList ts
  pretty (TyVar v) = text v

  prettyList ts = hsep $ map pretty ts

instance Pretty HscDecl where
  pretty (HashInclude s) = text "#include" <+> dquotes (text s)
  pretty (HashEnum tn cn tags) = text "#enum" <+> text tn <> comma <+> text cn <> comma
                             <+> align (vsep $ punctuate (comma <+> text "\\") $ map text tags)




















