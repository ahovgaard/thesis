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
          Var x             -> Set.singleton x
          Num _             -> Set.empty
          TrueLit           -> Set.empty
          FalseLit          -> Set.empty
          Add e1 e2         -> fvSet e1 `Set.union` fvSet e2
          LEq e1 e2         -> fvSet e1 `Set.union` fvSet e2
          If e1 e2 e3       -> fvSet e1 `Set.union` fvSet e2 `Set.union` fvSet e3
          Lam x tp e0       -> Set.delete x (fvSet e0)
          App e1 e2         -> fvSet e1 `Set.union` fvSet e2
          Let x e1 e2       -> fvSet e1 `Set.union` Set.delete x (fvSet e2)
          Pair e1 e2        -> fvSet e1 `Set.union` fvSet e2
          Fst e0            -> fvSet e0
          Snd e0            -> fvSet e0
          Record ls         -> Set.unions $ map (\(_, e) -> fvSet e) ls
          Select e0 x       -> fvSet e0
          ArrayLit es       -> Set.unions $ map fvSet es
          Index e0 e1       -> fvSet e0 `Set.union` fvSet e1
          Update e0 e1 e2   -> fvSet e0 `Set.union` fvSet e1 `Set.union` fvSet e2
          Length e0         -> fvSet e0
          Loop x e1 y e2 e3 -> fvSet e1 `Set.union` fvSet e2
                                        `Set.union` (Set.delete x $ Set.delete y $ fvSet e3)

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
                         Nothing -> -- throwError $ "variable " ++ x ++ " is out of scope"
                                    return Dynamic

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

  -- Handle special case of variable application to reduce the number of
  -- unnecessary let-bindings being created.
  App (Var f) e2 -> do sv1 <- lookupStaticVal f
                       case sv1 of
                         Lambda x tp e0 fv ->
                           do (e2', sv2) <- defunc e2
                              (e0', sv)  <- local (extendEnv x sv2) (defunc e0)
                              return (letBindFV f fv (Let x e2' e0'), sv)
                         _ -> error "applied variable is not a function"

  App e1 e2      -> do (e1', Lambda x tp e0 fv) <- defunc e1
                       (e2', sv2) <- defunc e2
                       (e0', sv) <- local (extendEnv x sv2) (defunc e0)
                       y <- freshVar "env"
                       return (Let y e1' (letBindFV y fv (Let x e2' e0')), sv)

  -- special case for variable application
  --App (Var f) e2 -> do sv1 <- lookupStaticVal f
  --                     case sv1 of
  --                       Lambda x tp e0 fv ->
  --                         -- TODO: need to handle case for non-dynamic arg
  --                         do (e2', sv2) <- defunc e2
  --                            case sv2 of
  --                              Dynamic  -> defunc (letBindFV f fv (subst x e2' e0))
  --                              Lambda{} -> do y <- freshVar "env"
  --                                             defunc $ letBindFV f fv (Let y e2' (subst x e2' e0))
  --                            --(e', sv) <- defunc $ subst x e2' e0
  --                            --return (letBindFV f fv e', sv)

  --                       _ -> throwError "application of non-function"

  --App e1 e2      -> do (e1', Lambda x tp e0 fv) <- defunc e1
  --                     (e2', Dynamic)           <- defunc e2
  --                     -- generate fresh variable for binding the closure of e1
  --                     y <- freshVar "env"
  --                     defunc $ Let y e1' (letBindFV y fv (subst x e2' e0))

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


-- Skips type checking. Convenient for testing.
defuncStr :: String -> IO ()
defuncStr s = case parseString s of
  Left parseErr -> print parseErr
  Right expr    ->
    case runDefM $ defunc expr of
      Left defErr      -> print defErr
      Right (expr, sv) -> print $ pretty expr


-- Simple haskeline REPL
process :: String -> IO ()
process s = case parseString s of
  Left  err  -> putStrLn "Parse error:" >> print err
  Right expr ->
    case typeOf emptyCtx expr of
      Left tpErr -> putStrLn $ "Type error: " ++ show tpErr
      Right tp   -> do
        putStrLn $ "Type: " ++ show tp
        case runDefM $ defunc expr of
          Left defErr -> putStrLn $ "Defunctionalization error: " ++ show defErr
          Right (expr, sv) -> do
            putStrLn $ "Top-level static value:\t" ++ show sv ++ "\n"
            putStrLn $ "Result program:\n"
            putStrLn . show $ pretty expr

main :: IO ()
main = runInputT defaultSettings loop
  where loop = do
          input <- getInputLine "> "
          case input of
            Nothing -> return ()
            Just "" -> loop
            Just s  -> liftIO (process s) >> loop
