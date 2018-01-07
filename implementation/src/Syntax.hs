module Syntax ( Name
              , Tp(..)
              , Expr(..)
              , freeVars
              , subst
              , order
              , pretty
              ) where

import qualified Data.Set as Set
import Text.PrettyPrint.Leijen

import Prelude hiding ((<$>))

type Name = String

-- Abstract syntax of types.
data Tp = TpInt
        | TpBool
        | TpArrow Tp Tp
        | TpPair Tp Tp
        | TpArray Tp
        | TpRecord [(Name, Tp)]
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

-- Computes the free variables of an expression in deterministic order.
freeVars :: Expr -> [Name]
freeVars = Set.elems . fvSet
  where fvSet expr = case expr of
          Var x             -> Set.singleton x
          Num _             -> Set.empty
          TrueLit           -> Set.empty
          FalseLit          -> Set.empty
          Add e1 e2         -> fvSet e1 `Set.union` fvSet e2
          LEq e1 e2         -> fvSet e1 `Set.union` fvSet e2
          If e1 e2 e3       -> fvSet e1 `Set.union` fvSet e2 `Set.union` fvSet e3
          Lam x _ e0        -> Set.delete x (fvSet e0)
          App e1 e2         -> fvSet e1 `Set.union` fvSet e2
          Let x e1 e2       -> fvSet e1 `Set.union` Set.delete x (fvSet e2)
          Pair e1 e2        -> fvSet e1 `Set.union` fvSet e2
          Fst e0            -> fvSet e0
          Snd e0            -> fvSet e0
          Record ls         -> Set.unions $ map (\(_, e) -> fvSet e) ls
          Select e0 _       -> fvSet e0
          ArrayLit es       -> Set.unions $ map fvSet es
          Index e0 e1       -> fvSet e0 `Set.union` fvSet e1
          Update e0 e1 e2   -> fvSet e0 `Set.union` fvSet e1 `Set.union` fvSet e2
          Length e0         -> fvSet e0
          Loop x e1 y e2 e3 -> fvSet e1 `Set.union` fvSet e2
                                        `Set.union` Set.delete x (Set.delete y $ fvSet e3)

-- Substitutes s for x in t.
-- Assumes that variables are unique for now.
subst :: Name -> Expr -> Expr -> Expr
subst x s t = case t of
  Var y
    | x == y           -> s
    | otherwise        -> t
  Num _                -> t
  TrueLit              -> t
  FalseLit             -> t
  Add e1 e2            -> Add (subst x s e1) (subst x s e2)
  LEq e1 e2            -> LEq (subst x s e1) (subst x s e2)
  If e1 e2 e3          -> If (subst x s e1) (subst x s e2) (subst x s e3)
  Lam y tp e0
    | x == y           -> t
    | otherwise        -> Lam y tp (subst x s e0)
  App e1 e2            -> App (subst x s e1) (subst x s e2)
  Let y e1 e2
    | x == y           -> Let y (subst x s e1) e2
    | otherwise        -> Let y (subst x s e1) (subst x s e2)
  Pair e1 e2           -> Pair (subst x s e1) (subst x s e2)
  Fst e0               -> Fst (subst x s e0)
  Snd e0               -> Snd (subst x s e0)

  Record ls            -> Record $ map (\(y,e) -> (y, subst x s e)) ls
  Select e0 y          -> Select (subst x s e0) y

  ArrayLit es          -> ArrayLit $ map (subst x s) es
  Index e0 e1          -> Index (subst x s e0) (subst x s e1)
  Update e0 e1 e2      -> Update (subst x s e0) (subst x s e1) (subst x s e2)
  Length e0            -> Length (subst x s e0)
  Loop y e1 z e2 e3    -> Loop y (subst x s e1) z (subst x s e2)
                               (if x == y || x == z then e3 else subst x s e3)

-- Order of a type.
order :: Tp -> Int
order TpInt             = 0
order TpBool            = 0
order (TpArrow tp1 tp2) = max (order tp1 + 1) (order tp2)
order (TpPair  tp1 tp2) = max (order tp1) (order tp2)
order (TpArray tp)      = order tp

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
  Add e1 e2         -> parens (pprExpr d e1) <+> char '+'  <+> parens (pprExpr d e2)
  LEq e1 e2         -> pprExpr d e1 <+> text "<=" <+> pprExpr d e2

  If e1 e2 e3       -> text "if" <+> pprExpr d e1
                                 <+> text "then" <+> pprExpr d e2
                                 <+> text "else" <+> pprExpr d e3

  Lam x tp e0       -> parensIf (d > 0) $
                         text "\\" <> text x <+> colon
                         <+> pretty tp <> dot <+> pprExpr (d+1) e0

  App e1 e2         -> parensIf (d > 0) $ pprExpr (d+1) e1 <+> pprExpr (d+1) e2

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
