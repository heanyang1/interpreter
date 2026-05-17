import AST
import Parser
import Evaluate
import TypeCheck
import TestRunner
import Test.HUnit

main :: IO Counts
main = runTestTT allTests

allTests :: Test
allTests = TestList
    [ testParser
    , testArithmetic
    , testConditional
    , testFunctions
    , testProduct
    , testSum
    , testFixpoints
    , testForall
    , testMoreTypeCheck
    , testTypeErrors
    ]

-- Parser
testParser :: Test
testParser = TestLabel "Parser" $ TestList
    [ TestLabel "lam_app" $ TestCase $ do
        case parse "fun x -> x y" of
            Left err -> assertFailure err
            Right (ELam _ (EApp (EVar _) (EVar _))) -> return ()
            Right e -> assertFailure $ "Unexpected AST: " ++ show e
        case (parse "x y z", parse "((x y) z)") of
            (Right e1, Right e2) -> assertEqual "app assoc" e1 e2
            _ -> assertFailure "Parse error"
        case (parse "fun x -> fun y -> x y", parse "fun x -> (fun y -> x y)") of
            (Right e1, Right e2) -> assertEqual "fun assoc" e1 e2
            _ -> assertFailure "Parse error"
    ]

-- Arithmetic
testArithmetic :: Test
testArithmetic = TestLabel "Arithmetic" $ TestList
    [ TestLabel "numbers" $ TestList
        [ t "1" (ENum 1) TNum, t "1234567" (ENum 1234567) TNum, t "0" (ENum 0) TNum ]
    , TestLabel "simple" $ TestList
        [ t "1+2" (ENum 3) TNum, t "1-2" (ENum (-1)) TNum
        , t "1*2" (ENum 2) TNum, t "1/2" (ENum 0) TNum ]
    , TestLabel "complex" $ t "1 +(1   *((2-3))+4)/( 5 +6)" (ENum 1) TNum
    ]

-- Conditional
testConditional :: Test
testConditional = TestLabel "Conditional" $ TestList
    [ TestLabel "relop" $ TestList
        [ t "1==1" ETrue TBool, t "1<2" ETrue TBool, t "2>1" ETrue TBool
        , t "1==2" EFalse TBool, t "2<1" EFalse TBool, t "1>2" EFalse TBool ]
    , TestLabel "and_or" $ TestList
        [ t "true && true" ETrue TBool, t "true && false" EFalse TBool
        , t "false && true" EFalse TBool, t "false && false" EFalse TBool
        , t "true || true" ETrue TBool, t "true || false" ETrue TBool
        , t "false || true" ETrue TBool, t "false || false" EFalse TBool ]
    , TestLabel "ifelse" $ TestList
        [ t "if true then 1 else 2" (ENum 1) TNum
        , t "if false then 1 else 2" (ENum 2) TNum
        , t "if false then 1*2 else (if true then 2+4 else 3/5)" (ENum 6) TNum ]
    , TestLabel "complex" $ TestList
        [ t "(1+2>3||4>5)&&4==5" EFalse TBool
        , t "if 1<2*3 then 3==4+1 else 4>5" EFalse TBool ]
    ]

-- Functions
testFunctions :: Test
testFunctions = TestLabel "Functions" $ TestList
    [ TestLabel "simple" $ TestList
        [ t "let f = fun x -> x + 1 in f 2" (ENum 3) TNum
        , t "(fun x -> x) 2" (ENum 2) TNum ]
    , TestLabel "shadow" $ t "let f = fun x -> fun x -> x in (f 0) 1" (ENum 1) TNum
    ]

-- Product
testProduct :: Test
testProduct = TestLabel "Product" $ TestList
    [ TestLabel "eval" $ TestList
        [ t "(1+2,3-4).L" (ENum 3) TNum
        , t "(1*2,3/4).R" (ENum 0) TNum
        , t "((1+2,3-4).L,(1*2,3/4).R).L" (ENum 3) TNum
        , tEval "(((),(1,2)),())" (EPair (EPair EUnit (EPair (ENum 1) (ENum 2))) EUnit)
        , tType "(((),(1,2)),())" (TProduct (TProduct TUnit (TProduct TNum TNum)) TUnit)
        ]
    ]

-- Sum
testSum :: Test
testSum = TestLabel "Sum" $ TestList
    [ TestLabel "eval" $ TestList
        [ t "case (inj 1=L) {L(l)->l+1|R(r)->3*r}" (ENum 2) TNum
        , t "let x = inj 1=R in case x {L(n)->(n.L)+1|R(n)->3*n}" (ENum 3) TNum
        , t "let x = (100,inj 1=R) in case x.R {L(n)->(n.L)+1|R(n)->3*n}" (ENum 3) TNum
        , t "let x = (inj 1 = R, inj (fun n -> n+1) = L).R in case x {L(f) -> (f 1) | R(n)->3*n}" (ENum 2) TNum
        ]
    ]

-- Fixpoints
testFixpoints :: Test
testFixpoints = TestLabel "Fixpoints" $ TestList
    [ TestLabel "desugar" $
        t "(fun fact -> fact 5) (fix fact -> (fun n -> if n == 0 then 1 else n * (fact (n - 1))))" (ENum 120) TNum
    , TestLabel "letrec" $
        t "letrec fact = fun n -> if n == 0 then 1 else n * (fact (n - 1)) in fact 5" (ENum 120) TNum
    ]

-- Forall / let-poly
testForall :: Test
testForall = TestLabel "Forall" $ TestList
    [ TestLabel "eval" $ TestList
        [ t "let id = fun x -> x in id 100" (ENum 100) TNum
        , t "let id = fun u -> fun x -> x in (id ()) 100" (ENum 100) TNum
        , t "let none = (inj () = L) in let some = fun x -> (inj x = R) in case (some 1) {L(x) -> 0 | R(n) -> n + 1}" (ENum 2) TNum
        ]
    , TestLabel "different_types" $
        t "let id = fun x -> x in if (id true) then (id 100) else 1" (ENum 100) TNum
    ]

-- More type check
testMoreTypeCheck :: Test
testMoreTypeCheck = TestLabel "MoreTypeCheck" $ TestList
    [ tType "()" TUnit
    , tType "true" TBool, tType "false" TBool
    , tType "1" TNum, tType "0" TNum
    , tType "1+2" TNum, tType "1-2" TNum, tType "1*2" TNum, tType "1/2" TNum
    , tType "1<2" TBool, tType "1>2" TBool, tType "1==2" TBool
    , tType "true && false" TBool, tType "true || false" TBool
    , tType "if true then 1 else 2" TNum
    , tType "if false then 1 else 2" TNum
    , tType "(fun x -> x) 1" TNum
    , tType "(fun x -> 1) 2" TNum
    , tType "let f = fun x -> x + 1 in f 2" TNum
    , tType "(1, true).L" TNum
    , tType "(1, true).R" TBool
    , tType "case inj 1 = L { L(x) -> x | R(y) -> y }" TNum
    , tType "fix f -> 1" TNum
    , tType "let f = fun x -> fun y -> x y in let g = f (fun x -> x) in g 1" TNum
    , tTypeError "x"
    , TestLabel "free_var" $ TestCase $ do
        case checkType "let id = fun x -> x in id" of
            Left err -> assertFailure err
            Right (TForall a (TFn arg ret)) -> do
                let showA = show a
                assertBool "arg is TVar a" $ case arg of TVar (Variable v) -> v == showA; _ -> False
                assertBool "ret is TVar a" $ case ret of TVar (Variable v) -> v == showA; _ -> False
            Right ty -> assertFailure $ "Expected forall fn, got " ++ show ty
    , TestLabel "fn_const" $ TestCase $ do
        case checkType "fun x -> true && x" of
            Left err -> assertFailure err
            Right (TFn arg ret) -> assertEqual "fn_const" (TFn TBool TBool) (TFn arg ret)
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty
    , TestLabel "fn_nested" $ TestCase $ do
        case checkType "let f = fun x -> fun y -> x + y in f" of
            Left err -> assertFailure err
            Right (TForall _ (TFn arg (TFn arg2 ret2))) ->
                assertEqual "fn_nested" (TFn TNum (TFn TNum TNum)) (TFn arg (TFn arg2 ret2))
            Right (TFn arg (TFn arg2 ret2)) ->
                assertEqual "fn_nested" (TFn TNum (TFn TNum TNum)) (TFn arg (TFn arg2 ret2))
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty
    , TestLabel "fn_passing_fn" $ TestCase $ do
        case checkType "fun f -> (f true) < 2" of
            Left err -> assertFailure err
            Right (TFn (TFn arg2 ret2) TBool) ->
                assertEqual "fn_passing_fn arg" TBool arg2 >> assertEqual "fn_passing_fn ret" TNum ret2
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty
    , TestLabel "pair_type" $ TestCase $ do
        case checkType "(1, true)" of
            Left err -> assertFailure err
            Right (TProduct l r) -> assertEqual "pair" (TProduct TNum TBool) (TProduct l r)
            Right ty -> assertFailure $ "Expected product, got " ++ show ty
    , TestLabel "inject_left" $ TestCase $ do
        case checkType "inj 1 = L" of
            Left err -> assertFailure err
            Right (TForall _ (TSum l _)) -> assertEqual "inject left" TNum l
            Right (TSum l _) -> assertEqual "inject left" TNum l
            Right ty -> assertFailure $ "Unexpected: " ++ show ty
    , TestLabel "inject_right" $ TestCase $ do
        case checkType "inj true = R" of
            Left err -> assertFailure err
            Right (TForall _ (TSum _ r)) -> assertEqual "inject right" TBool r
            Right (TSum _ r) -> assertEqual "inject right" TBool r
            Right ty -> assertFailure $ "Unexpected: " ++ show ty
    , TestLabel "letrec_type" $ TestCase $ do
        case checkType "letrec f = fun x -> if x == 0 then 0 else (f (x - 1)) + 1 in f" of
            Left err -> assertFailure err
            Right (TFn arg ret) -> assertEqual "letrec_type" (TFn TNum TNum) (TFn arg ret)
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty
    , TestLabel "polymorphism" $ TestCase $ do
        case checkType "let id = fun x -> x in let f = fun y -> y in (id true, f 1)" of
            Left err -> assertFailure err
            Right (TProduct l r) -> assertEqual "poly" (TProduct TBool TNum) (TProduct l r)
            Right ty -> assertFailure $ "Expected product, got " ++ show ty
    ]

-- Type errors
testTypeErrors :: Test
testTypeErrors = TestLabel "TypeErrors" $ TestList
    [ TestLabel "arithmetic" $ TestList
        [ tTypeError "1+()", tTypeError "()-()" ]
    , TestLabel "conditionals" $ TestList
        [ tTypeError "true || 1", tTypeError "() && true"
        , tTypeError "if true then 1 else ()", tTypeError "if 0 then 1 else 2"
        , tTypeError "1==()", tTypeError "(fun x -> x)>1" ]
    , TestLabel "functions" $ TestList
        [ tTypeError "x", tTypeError "1 ()" ]
    , TestLabel "adt" $ TestList
        [ tTypeError "1.L", tTypeError "case () {L(l)->l+1|R(r)->3*r}"
        , tTypeError "1*(1,2)", tTypeError "(inj 1=L)/1", tTypeError "1<(2,3)" ]
    , TestLabel "fixpoints" $ tTypeError "letrec f = 5 in f 1"
    ]