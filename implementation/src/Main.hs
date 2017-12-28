module Main (main) where

import Control.Monad.Trans
import System.Console.Haskeline

import Defunc
import Parser
import Syntax
import TypeChecker

-- Simple haskeline REPL
process :: String -> IO ()
process s = case parseString s of
  Left  parseErr -> putStrLn "Parse error:" >> print parseErr
  Right e        ->
    case typeOf emptyCtx e of
      Left tpErr -> putStrLn $ "Type error: " ++ show tpErr
      Right tp   -> do
        putStrLn $ "Type: " ++ show (pretty tp)
        case runDefM $ defunc e of
          Left defErr -> putStrLn $ "Defunctionalization error: " ++ show defErr
          Right (e', sv) -> do
            putStrLn $ "Top-level static value:\t" ++ show sv ++ "\n"
            putStrLn "Result program:\n"
            print $ pretty e'

main :: IO ()
main = runInputT defaultSettings loop
  where loop = do
          input <- getInputLine "> "
          case input of
            Nothing -> return ()
            Just "" -> loop
            Just s  -> liftIO (process s) >> loop
