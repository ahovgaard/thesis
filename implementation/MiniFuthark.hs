{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MiniFuthark where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans
import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.Haskeline

import Syntax
import Parser
import TypeChecker


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
  ArrayLit es          -> ArrayLit $ map (subst x s) es
  Index e0 e1          -> Index (subst x s e0) (subst x s e1)
  Update e0 e1 e2      -> Update (subst x s e0) (subst x s e1) (subst x s e2)
  Length e0            -> Length (subst x s e0)
  Loop y e1 z e2 e3    -> Loop y (subst x s e1) z (subst x s e2)
                               (if x == y || x == z then e3 else subst x s e3)



data StaticVal = Dynamic
               | Lambda Name Tp Expr [Name]
               | Tuple StaticVal StaticVal
               | Rcd [(Name, StaticVal)]
  deriving (Show, Eq)

type Env = [(Name, StaticVal)]

emptyEnv :: Env
emptyEnv = []

extendEnv :: Name -> StaticVal -> Env -> Env
extendEnv x sv env = (x, sv) : env

-- Computes the free variables of an expression in deterministic order.
freeVars :: Expr -> [Name]
freeVars = Set.elems . fvSet
  where fvSet expr = case expr of
          Var x       -> Set.singleton x
          Num _       -> Set.empty
          TrueLit     -> Set.empty
          FalseLit    -> Set.empty
          Add e1 e2   -> fvSet e1 `Set.union` fvSet e2
          LEq e1 e2   -> fvSet e1 `Set.union` fvSet e2
          Lam x tp e0 -> Set.delete x (fvSet e0)
          App e1 e2   -> fvSet e1 `Set.union` fvSet e2
          Let x e1 e2 -> fvSet e1 `Set.union` Set.delete x (fvSet e2)
          -- todo: finish

-- Generates a nested sequence of let-bindings, binding the free
-- variables to the corresponding fields in a record.
letBindFV :: Name -> [Name] -> Expr -> Expr
letBindFV _ []     e = e
letBindFV x (y:ys) e = Let y (Select (Var x) y) $ letBindFV x ys e


-- Defunctionalization monad.
newtype DefM a = DefM (ReaderT Env
                       (StateT Int
                        (Except String)) a)
  deriving (Monad, Functor, Applicative,
            MonadReader Env,
            MonadState Int,
            MonadError String)

runDefM :: DefM a -> Either String a
runDefM (DefM m) = runExcept . flip evalStateT 0 $ runReaderT m emptyEnv

lookupStaticVal :: Name -> DefM StaticVal
lookupStaticVal x = do env <- ask
                       case lookup x env of
                         Just sv -> return sv
                         Nothing -> throwError $ "variable " ++ x ++ " is out of scope"

freshVar :: Name -> DefM Name
freshVar x = do s <- get
                put (s+1)
                return $ x ++ show s


defunc :: Expr -> DefM (Expr, StaticVal)
defunc expr = case expr of
  Var x          -> do sv <- lookupStaticVal x
                       return (expr, sv)
  Num n          -> return (expr, Dynamic)
  TrueLit        -> return (expr, Dynamic)
  FalseLit       -> return (expr, Dynamic)

  Add e1 e2      -> do (e1', sv1) <- defunc e1
                       (e2', sv2) <- defunc e2
                       unless (sv1 == Dynamic && sv2 == Dynamic)
                         $ throwError "addition with static operand(s)"
                       return (Add e1' e2', Dynamic)

  Lam x tp e0    -> let fv = freeVars expr
                    in return (Record $ map (\s -> (s, Var s)) fv,
                               Lambda x tp e0 fv)

  -- special case for variable application
  App (Var f) e2 -> do sv1 <- lookupStaticVal f
                       case sv1 of
                         Lambda x tp e0 fv ->
                           -- TODO: need to handle case for non-dynamic arg
                           do (e2', Dynamic) <- defunc e2
                              defunc (letBindFV f fv (subst x e2' e0))
                         _ -> throwError "application of non-function"

  App e1 e2      -> do (e1', Lambda x tp e0 fv) <- defunc e1
                       (e2', Dynamic)           <- defunc e2
                       -- generate fresh variable for binding the closure of e1
                       y <- freshVar "env"
                       defunc $ Let y e1' (letBindFV y fv (subst x e2' e0))

  Let x e1 e2    -> do (e1', sv1) <- defunc e1
                       (e2', sv)  <- local (extendEnv x sv1) (defunc e2)
                       return (Let x e1' e2', sv)

  Pair e1 e2     -> do (e1', sv1) <- defunc e1
                       (e2', sv2) <- defunc e2
                       return (Pair e1' e2', Tuple sv1 sv2)

  Fst e0         -> do (e0', sv0) <- defunc e0
                       case sv0 of
                         Tuple sv1 _ -> return (Fst e0', sv1)
                         Dynamic     -> return (Fst e0', sv0)
                         _ -> error $ "projection of an expression that is neither "
                                   ++ "dynamic nor a statically known pair"

  Snd e0         -> do (e0', sv0) <- defunc e0
                       case sv0 of
                         Tuple _ sv2 -> return (Fst e0', sv2)
                         Dynamic     -> return (Fst e0', sv0)
                         _ -> error $ "projection of an expression that is neither "
                                   ++ "dynamic nor a statically known pair"

  Select e0 l    -> return (expr, Dynamic)
  -- Select e0 l    -> do (e0', sv0) <- defunc e0
  --                      case sv0 of
  --                        Dynamic -> return (expr, Dynamic)
  --                        Rcd svs -> case lookup l svs of
  --                          Just sv -> return (Select e0' l, sv)
  --                          Nothing -> error "invalid record projection2"
  --                        _ -> error $ "case for select: " ++ show sv0

  Record ls      -> do ls'' <- mapM (\(x,e) -> do (e', sv) <- defunc e
                                                  return ((x, e'), (x, sv))
                                    ) ls
                       let (ls', svs) = unzip ls''
                       return (Record ls', Rcd svs)

  _ -> error $ "missing case for: " ++ show expr


defuncStr s = case parseString s of
  Left err   -> print err
  Right expr -> print . runDefM $ defunc expr


-- Simple haskeline REPL
process :: String -> IO ()
process s = case parseString s of
  Left  err  -> putStrLn "Parse error:" >> print err
  Right expr ->
    case typeOf emptyCtx expr of
      Left tpErr -> putStrLn $ "Type error: " ++ show tpErr
      Right tp   -> do
        putStrLn $ "Type:\n\t"   ++ show tp
        putStrLn $ "Result:\n\t" ++ (show . runDefM $ defunc expr)

main :: IO ()
main = runInputT defaultSettings loop
  where loop = do
          input <- getInputLine "> "
          case input of
            Nothing -> return ()
            Just "" -> loop
            Just s  -> liftIO (process s) >> loop

-- -- Examples.
-- ex1 = process "(\\f:int->int. \\x:int. f (f x)) (\\y:int. y + y)"
--
-- ex2 = process "(\\f:(int->int)->(int->int). f) (\\g:int->int. g) (\\h:int. h)"
--
-- ex3 = process $ unlines [ "let comp = (\\f:int->int. \\g:int->int. \\x:int. f (g x))"
--                         , "in comp (\\y:int. if y <= 10 then y+y else y+1)"
--                         , "        (\\z:int. z+z)"
--                         ]
--
-- ex4 = process $ unlines [ "\\b:bool. \\m:int. \\n:int."
--                         , "  let f = \\g:int->int. \\x:int. if b then g x else g (g x) in"
--                         , "  let h = \\y:int. y + y in"
--                         , "  let k = \\z:int. z + 1"
--                         , "  in f h m + f h n + f k m + f k n"
--                         ]
--
-- ex5 = process $ unlines [ "\\x:int. let f = \\g:(int->int)->int. g (\\y:int. y+y)"
--                         , "         in f (\\h:int->int. h x) + f (\\h:int->int. h (h x))"
--                         ]
