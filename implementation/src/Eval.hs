module Eval (eval) where

import Control.Monad (foldM)

import Syntax

eval :: Expr -> Maybe Expr
eval expr = case expr of
  Var _             -> Nothing
  Num _             -> Just expr
  TrueLit           -> Just TrueLit
  FalseLit          -> Just FalseLit

  Add e1 e2         -> do Num n1 <- eval e1
                          Num n2 <- eval e2
                          Just $ Num (n1 + n2)

  LEq e1 e2         -> do Num n1 <- eval e1
                          Num n2 <- eval e2
                          Just $ if n1 <= n2 then TrueLit else FalseLit

  If e1 e2 e3       -> do v1 <- eval e1
                          case v1 of
                            TrueLit  -> eval e2
                            FalseLit -> eval e3
                            _        -> Nothing

  Lam{}             -> Just expr

  App e1 e2         -> do v1 <- eval e1
                          v2 <- eval e2
                          case v1 of
                            Lam x _ e0 -> eval $ subst x v2 e0
                            _          -> Nothing

  Let x e1 e2       -> do v1 <- eval e1
                          eval $ subst x v1 e2

  Pair e1 e2        -> do v1 <- eval e1
                          v2 <- eval e2
                          Just $ Pair v1 v2

  Fst e0            -> do v0 <- eval e0
                          case v0 of
                            Pair v1 _ -> Just v1
                            _         -> Nothing

  Snd e0            -> do v0 <- eval e0
                          case v0 of
                            Pair _ v2 -> Just v2
                            _         -> Nothing

  Record ls         -> do let (xs, es) = unzip ls
                          vs <- mapM eval es
                          Just . Record $ zip xs vs

  Select e0 x       -> do v0 <- eval e0
                          case v0 of
                            Record ls -> lookup x ls
                            _         -> Nothing

  ArrayLit es       -> ArrayLit <$> mapM eval es

  Index e0 e1       -> do v0 <- eval e0
                          v1 <- eval e1
                          case v0 of
                            ArrayLit vs ->
                              case v1 of
                                Num i | 0 <= i && i < length vs -> Just $ vs !! i
                                _                               -> Nothing
                            _           -> Nothing

  Update e0 e1 e2   -> do v0 <- eval e0
                          v1 <- eval e1
                          v2 <- eval e2
                          case v0 of
                            ArrayLit vs ->
                              case v1 of
                                Num i | i < length vs ->
                                        Just . ArrayLit $ take i vs ++ (v2 : drop (i+1) vs)
                                _ -> Nothing
                            _ -> Nothing

  Length e0         -> do v0 <- eval e0
                          case v0 of
                            ArrayLit vs -> Just . Num $ length vs
                            _           -> Nothing

  Loop x e1 y e2 e3 -> do v1    <- eval e1
                          Num n <- eval e2
                          let iter val i = eval (subst y (Num i) (subst x val e3))
                          foldM iter v1 [0..n-1]
