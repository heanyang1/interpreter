module TestRunner where

import AST
import Parser
import TypeCheck
import Evaluate
import Test.HUnit

evalExpr :: String -> Either String Expr
evalExpr s = case parse s of
    Left err -> Left err
    Right e -> Right (eval e)

checkType :: String -> Either String Type
checkType s = case parse s of
    Left err -> Left err
    Right e -> typeCheck e

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