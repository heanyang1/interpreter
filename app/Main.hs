module Main where

import AST
import ASTUtil (Symbol (..))
import qualified Control.Monad
import DotGen
import Evaluate
import Flags
import Parser
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (IOMode (..), getContents, hGetContents, hPutStrLn, readFile, stderr, withFile)
import TypeCheck

parseMode :: String -> Maybe Mode
parseMode "parse" = Just Parse
parseMode "eval" = Just Eval
parseMode "verbose" = Just Verbose
parseMode "very-verbose" = Just VeryVerbose
parseMode _ = Nothing

parseOutput :: String -> Maybe OutputMode
parseOutput "full" = Just Full
parseOutput "simplified" = Just Simplified
parseOutput "debruijn" = Just DeBruijn
parseOutput "graphviz" = Just Graphviz
parseOutput _ = Nothing

die :: String -> IO a
die msg = hPutStrLn stderr msg >> exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    [m, o] -> run m o Nothing
    [m, o, p] -> run m o (Just p)
    _ -> do
      hPutStrLn stderr "Usage: interpreter <mode> <output> [input_path]"
      hPutStrLn stderr "  mode: parse | eval | verbose | very-verbose"
      hPutStrLn stderr "  output: full | simplified | debruijn | graphviz"
      exitFailure

run :: String -> String -> Maybe String -> IO ()
run modeStr outputStr mpath = do
  mode <- maybe (die "Invalid mode") return (parseMode modeStr)
  output <- maybe (die "Invalid output mode") return (parseOutput outputStr)
  input <- maybe getContents readFile mpath
  case parse input of
    Left err -> die $ "Parse error: " ++ err
    Right ast -> process mode output ast

process :: Mode -> OutputMode -> Expr -> IO ()
process Parse output ast =
  putStrLn $ formatAst ast output Nothing
process mode output ast = do
  let dbAst = toDebruijn ast
  case typeCheck mode dbAst of
    Left err -> die $ "Type error: " ++ err
    Right ty -> do
      Control.Monad.when (mode == Verbose || mode == VeryVerbose) $
        putStrLn $
          formatType ty output
      Control.Monad.when (output == Graphviz) $ putStrLn "digraph Program {"
      case mode of
        VeryVerbose -> do
          putStrLn $ formatAst dbAst output (Just "step-0")
          printSteps 1 dbAst output
        _ -> putStrLn $ formatAst (eval dbAst) output (Just "last")
      Control.Monad.when (output == Graphviz) $ putStrLn "}"

printSteps :: Int -> Expr -> OutputMode -> IO ()
printSteps i e output = case tryStep e of
  Val -> return ()
  Step e' -> do
    putStrLn $ formatAst e' output (Just $ "step-" ++ show i)
    printSteps (i + 1) e' output
