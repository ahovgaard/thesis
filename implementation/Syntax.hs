module Syntax where

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
          | ArrayLit [Expr]
          | Index Expr Expr
          | Update Expr Expr Expr
          | Length Expr
          | Loop Name Expr Name Expr Expr
  deriving (Show)
