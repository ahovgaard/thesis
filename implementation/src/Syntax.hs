module Syntax ( Name
              , Tp(..)
              , Expr(..)
              , pretty
              ) where

import Text.PrettyPrint.Leijen

import Prelude hiding ((<$>))

type Name = String

-- Abstract syntax of types.
data Tp = TpInt
        | TpBool
        | TpArrow Tp Tp
        | TpPair Tp Tp
        | TpArray Tp
  deriving (Show, Eq)

-- Abstract syntax of expressions.
data Expr = Var Name
          | Num Int
          | TrueLit
          | FalseLit
          | Add Expr Expr
          | LEq Expr Expr
          | If Expr Expr Expr
          | Lam Name Tp Expr
          | App Expr Expr
          | Let Name Expr Expr
          | Pair Expr Expr
          | Fst Expr
          | Snd Expr
          | Record [(Name, Expr)]
          | Select Expr Name
          | ArrayLit [Expr]
          | Index Expr Expr
          | Update Expr Expr Expr
          | Length Expr
          | Loop Name Expr Name Expr Expr
  deriving (Show, Eq)

-- Pretty printing of expression and types.
instance Pretty Expr where
  pretty = pprExpr 0

instance Pretty Tp where
  pretty = pprType 0

pprExpr :: Int -> Expr -> Doc
pprExpr d e = case e of
  Var x             -> text x
  Num n             -> int n
  TrueLit           -> text "true"
  FalseLit          -> text "false"
  Add e1 e2         -> pprExpr d e1 <+> char '+'  <+> pprExpr d e2
  LEq e1 e2         -> pprExpr d e1 <+> text "<=" <+> pprExpr d e2

  If e1 e2 e3       -> text "if" <+> pprExpr d e1
                                 <+> text "then" <+> pprExpr d e2
                                 <+> text "else" <+> pprExpr d e3

  Lam x tp e0       -> parensIf (d > 0) $
                         text "\\" <> text x <+> colon
                         <+> pretty tp <> dot <+> pprExpr (d+1) e0

  App e1 e2         -> parensIf (d > 0) $ pprExpr (d+1) e1 <+> pprExpr d e2

  Let x e1 e2       -> align $  (text "let" <+> text x <+> equals <+> pprExpr d e1)
                            <$> (text "in"  <+> pprExpr d e2)

  Pair e1 e2        -> parens $ pprExpr d e1 <> text ", " <> pprExpr d e2
  Fst e0            -> parensIf (d > 0) $ text "fst" <+> pprExpr (d+1) e0
  Snd e0            -> parensIf (d > 0) $ text "snd" <+> pprExpr (d+1) e0

  Record ls         -> encloseSep lbrace rbrace (comma <> space) (map pprField ls)
    where pprField (x, e') = text x <+> equals <+> pprExpr d e'

  Select e0 l       -> pprExpr (d+1) e0 <> dot <> text l

  ArrayLit es       -> parensIf (d > 0) $ list $ map (pprExpr d) es
  Index e0 e1       -> pprExpr (d+1) e0 <> brackets (pprExpr d e1)
  Update e0 e1 e2   -> pprExpr (d+1) e0 <+> text "with" <+> brackets (pprExpr d e1)
                                        <+> text "<-"   <+> pprExpr (d+1) e2
  Length e0         -> text "length" <+> pprExpr (d+1) e0

  Loop x e1 y e2 e3 -> text "loop" <+> text x <+> equals   <+> pprExpr d e1 <+>
                       text "for"  <+> text y <+> text "<" <+> pprExpr d e2 <+>
                       text "do"   <+> pprExpr d e3

pprType :: Int -> Tp -> Doc
pprType d tp = case tp of
  TpInt           -> text "int"
  TpBool          -> text "bool"
  TpArrow tp1 tp2 -> parensIf (d > 0)
                       $ pprType (d+1) tp1 <+> text "->" <+> pprType d tp2
  TpPair tp1 tp2  -> parens $ pprType d tp1 <> text ", " <> pprType d tp2
  TpArray tp0     -> text "[]" <> pprType d tp0

-- Enclose document in parenthesis if condition holds.
parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id
