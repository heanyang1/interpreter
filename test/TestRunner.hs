module TestRunner where

import AST
import ASTUtil (Symbol (..))
import Control.Exception (ErrorCall, evaluate, try)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import DotGen
import Evaluate
import Flags
import Parser
import Test.HUnit
import TypeCheck
import UnionFind

alphaEqType :: Type -> Type -> Bool
alphaEqType = go Map.empty Map.empty
  where
    go lm rm (TFn a r) (TFn a' r') = go lm rm a a' && go lm rm r r'
    go lm rm (TProduct l r) (TProduct l' r') = go lm rm l l' && go lm rm r r'
    go lm rm (TSum l r) (TSum l' r') = go lm rm l l' && go lm rm r r'
    go lm rm (TForall v t) (TForall v' t') =
      let n = show (Map.size lm)
          c = VName n
       in go (Map.insert v c lm) (Map.insert v' c rm) t t'
    go lm rm (TMu v t) (TMu v' t') =
      let n = show (Map.size lm)
          c = VName n
       in go (Map.insert v c lm) (Map.insert v' c rm) t t'
    go lm rm (TVar v) (TVar v') =
      let resolve m x = Map.findWithDefault x x m
       in resolve lm v == resolve rm v'
    go _ _ TNum TNum = True
    go _ _ TBool TBool = True
    go _ _ TUnit TUnit = True
    go _ _ _ _ = False

tStep :: String -> Test
tStep s = TestCase $ do
  e <- case parse s of
    Left err -> assertFailure $ "Parse error: " ++ err
    Right e -> return e
  let db = toDebruijn e
  ty <- case typeCheck db of
    Left err -> assertFailure $ "Type error on original: " ++ err
    Right ty -> return ty
  case tryStep db of
    Val -> assertFailure $ "Expression is already a value: " ++ s
    Step e' -> do
      ty' <- case typeCheck e' of
        Left err -> assertFailure $ "Type error after step: " ++ err
        Right ty' -> return ty'
      assertBool
        ("Type mismatch for " ++ show s ++ "\n  before: " ++ show ty ++ "\n  after:  " ++ show ty')
        (alphaEqType ty ty')

evalExpr :: String -> Either String Expr
evalExpr s = case parse s of
  Left err -> Left err
  Right e -> Right (eval (toDebruijn e))

checkType :: String -> Either String Type
checkType s = case parse s of
  Left err -> Left err
  Right e -> typeCheck (toDebruijn e)

t :: String -> Expr -> Type -> Test
t s val ty = TestCase $ do
  case evalExpr s of
    Left err -> assertFailure $ "Eval error: " ++ err
    Right result -> assertEqual ("eval " ++ show s) val result
  case checkType s of
    Left err -> assertFailure $ "Type error: " ++ err
    Right result -> assertEqual ("type " ++ show s) ty result

tEval :: String -> Expr -> Test
tEval s val = TestCase $
  case evalExpr s of
    Left err -> assertFailure $ "Eval error: " ++ err
    Right result -> assertEqual ("eval " ++ show s) val result

tType :: String -> Type -> Test
tType s ty = TestCase $
  case checkType s of
    Left err -> assertFailure $ "Type error: " ++ err
    Right result -> assertEqual ("type " ++ show s) ty result

tTypeError :: String -> Test
tTypeError s = TestCase $
  case checkType s of
    Left _ -> return ()
    Right ty -> assertFailure $ "Expected type error but got " ++ show ty

tFormatAst :: String -> OutputMode -> Maybe String -> String -> Test
tFormatAst s mode name expected = TestCase $
  case parse s of
    Left err -> assertFailure $ "Parse error: " ++ err
    Right e ->
      assertEqual
        ("formatAst " ++ show s ++ " " ++ show mode)
        expected
        (formatAst e mode name)

tFormatType :: String -> OutputMode -> String -> Test
tFormatType s mode expected = TestCase $
  case checkType s of
    Left err -> assertFailure $ "Type error: " ++ err
    Right ty ->
      assertEqual
        ("formatType " ++ show s ++ " " ++ show mode)
        expected
        (formatType ty mode)

tShow :: String -> String -> Test
tShow s expected = TestCase $
  case parse s of
    Left err -> assertFailure $ "Parse error: " ++ err
    Right e -> assertEqual ("show " ++ show s) expected (show e)

tShowType :: String -> String -> Test
tShowType s expected = TestCase $
  case checkType s of
    Left err -> assertFailure $ "Type error: " ++ err
    Right ty -> assertEqual ("show type " ++ show s) expected (show ty)

tParseError :: String -> Test
tParseError s = TestCase $
  case parse s of
    Left _ -> return ()
    Right e -> assertFailure $ "Expected parse error but got " ++ show e
