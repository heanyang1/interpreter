module Main where

import AST
import ASTUtil (Symbol(..))
import Parser
import Evaluate
import TypeCheck
import Flags
import DotGen
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr, getContents, readFile, IOMode(..), withFile, hGetContents)
import qualified Control.Monad

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
    let mode = parseMode modeStr
    let output = parseOutput outputStr
    case (mode, output) of
        (Nothing, _) -> die "Invalid mode"
        (_, Nothing) -> die "Invalid output mode"
        (Just m, Just o) -> do
            input <- maybe getContents readFile mpath
            case parse input of
                Left err -> die $ "Parse error: " ++ err
                Right ast -> case m of
                    Parse -> putStrLn $ formatAst ast o Nothing
                    _ -> do
                        case typeCheck ast of
                            Left err -> die $ "Type error: " ++ err
                            Right ty -> do
                                Control.Monad.when (m == Verbose || m == VeryVerbose)
                                    $ putStrLn $ formatType ty o
                                Control.Monad.when (o == Graphviz) $ putStrLn "digraph Program {"
                                putStrLn $ formatAst (eval ast) o (Just "last")
                                Control.Monad.when (o == Graphviz) $ putStrLn "}"
