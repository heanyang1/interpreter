module Flags where

import AST
import ASTUtil (Symbol (..))
import DotGen
import Text.Read (readMaybe)

data Mode
  = Parse
  | Eval
  | Verbose
  | VeryVerbose
  deriving (Show, Eq)

data OutputMode
  = Full
  | Simplified
  | DeBruijn
  | Graphviz
  deriving (Show, Eq)

formatAst :: Expr -> OutputMode -> Maybe String -> String
formatAst ast outputMode name = case outputMode of
  Full -> show ast
  Simplified -> show (toDebruijn ast)
  DeBruijn -> show (toDebruijn ast)
  Graphviz -> toDot ast name

formatType :: Type -> OutputMode -> String
formatType ty outputMode = case outputMode of
  Full -> show ty
  Simplified -> show ty
  DeBruijn -> show (toDebruijn ty)
  Graphviz -> ""