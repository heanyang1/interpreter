import AST
import ASTUtil (Symbol(..))
import qualified Data.Map.Strict as Map
import Data.List (isPrefixOf, isInfixOf)
import Evaluate
import Flags
import Parser
import Test.HUnit
import TestRunner
import TypeCheck
import UnionFind

main :: IO Counts
main = runTestTT allTests

allTests :: Test
allTests =
  TestList
    [ testParser,
      testArithmetic,
      testConditional,
      testFunctions,
      testProduct,
      testSum,
      testFixpoints,
      testForall,
      testMoreTypeCheck,
      testTypeErrors,
      testTypePreservation,
      testFlags,
      testDotGen,
      testUnionFind,
      testTryStep,
      testShowInstances,
      testTypeCheckUtil,
      testParseErrors,
      testAnnotations
    ]

-- Parser
testParser :: Test
testParser =
  TestLabel "Parser" $
    TestList
      [ TestLabel "lam_app" $ TestCase $ do
          case parse "fun x -> x y" of
            Left err -> assertFailure err
            Right (ELam _ _ (EApp (EVar _) (EVar _))) -> return ()
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
testArithmetic =
  TestLabel "Arithmetic" $
    TestList
      [ TestLabel "numbers" $
          TestList
            [t "1" (ENum 1) TNum, t "1234567" (ENum 1234567) TNum, t "0" (ENum 0) TNum],
        TestLabel "simple" $
          TestList
            [ t "1+2" (ENum 3) TNum,
              t "1-2" (ENum (-1)) TNum,
              t "1*2" (ENum 2) TNum,
              t "1/2" (ENum 0) TNum
            ],
        TestLabel "complex" $ t "1 +(1   *((2-3))+4)/( 5 +6)" (ENum 1) TNum
      ]

-- Conditional
testConditional :: Test
testConditional =
  TestLabel "Conditional" $
    TestList
      [ TestLabel "relop" $
          TestList
            [ t "1==1" ETrue TBool,
              t "1<2" ETrue TBool,
              t "2>1" ETrue TBool,
              t "1==2" EFalse TBool,
              t "2<1" EFalse TBool,
              t "1>2" EFalse TBool
            ],
        TestLabel "and_or" $
          TestList
            [ t "true && true" ETrue TBool,
              t "true && false" EFalse TBool,
              t "false && true" EFalse TBool,
              t "false && false" EFalse TBool,
              t "true || true" ETrue TBool,
              t "true || false" ETrue TBool,
              t "false || true" ETrue TBool,
              t "false || false" EFalse TBool
            ],
        TestLabel "ifelse" $
          TestList
            [ t "if true then 1 else 2" (ENum 1) TNum,
              t "if false then 1 else 2" (ENum 2) TNum,
              t "if false then 1*2 else (if true then 2+4 else 3/5)" (ENum 6) TNum
            ],
        TestLabel "complex" $
          TestList
            [ t "(1+2>3||4>5)&&4==5" EFalse TBool,
              t "if 1<2*3 then 3==4+1 else 4>5" EFalse TBool
            ]
      ]

-- Functions
testFunctions :: Test
testFunctions =
  TestLabel "Functions" $
    TestList
      [ TestLabel "simple" $
          TestList
            [ t "let f = fun x -> x + 1 in f 2" (ENum 3) TNum,
              t "(fun x -> x) 2" (ENum 2) TNum
            ],
        TestLabel "shadow" $ t "let f = fun x -> fun x -> x in (f 0) 1" (ENum 1) TNum,
        TestLabel "complex" $
          TestList
            [ t "(fun x -> fun y -> x y) (fun x -> x) 2" (ENum 2) TNum,
              t "(fun x -> fun y -> y x) 2 (fun x -> x)" (ENum 2) TNum
            ]
      ]

-- Product
testProduct :: Test
testProduct =
  TestLabel "Product" $
    TestList
      [ TestLabel "eval" $
          TestList
            [ t "(1+2,3-4).L" (ENum 3) TNum,
              t "(1*2,3/4).R" (ENum 0) TNum,
              t "((1+2,3-4).L,(1*2,3/4).R).L" (ENum 3) TNum,
              tEval "(((),(1,2)),())" (EPair (EPair EUnit (EPair (ENum 1) (ENum 2))) EUnit),
              tType "(((),(1,2)),())" (TProduct (TProduct TUnit (TProduct TNum TNum)) TUnit)
            ]
      ]

-- Sum
testSum :: Test
testSum =
  TestLabel "Sum" $
    TestList
      [ TestLabel "eval" $
          TestList
            [ t "case (inj 1=L) {L(l)->l+1|R(r)->3*r}" (ENum 2) TNum,
              t "let x = inj 1=R in case x {L(n)->(n.L)+1|R(n)->3*n}" (ENum 3) TNum,
              t "let x = (100,inj 1=R) in case x.R {L(n)->(n.L)+1|R(n)->3*n}" (ENum 3) TNum,
              t "let x = (inj 1 = R, inj (fun n -> n+1) = L).R in case x {L(f) -> (f 1) | R(n)->3*n}" (ENum 2) TNum
            ]
      ]

-- Fixpoints
testFixpoints :: Test
testFixpoints =
  TestLabel "Fixpoints" $
    TestList
      [ TestLabel "desugar" $
          t "(fun fact -> fact 5) (fix fact -> (fun n -> if n == 0 then 1 else n * (fact (n - 1))))" (ENum 120) TNum,
        TestLabel "letrec" $
          t "letrec fact = fun n -> if n == 0 then 1 else n * (fact (n - 1)) in fact 5" (ENum 120) TNum
      ]

-- Forall / let-poly
testForall :: Test
testForall =
  TestLabel "Forall" $
    TestList
      [ TestLabel "eval" $
          TestList
            [ t "let id = fun x -> x in id 100" (ENum 100) TNum,
              t "let id = fun u -> fun x -> x in (id ()) 100" (ENum 100) TNum,
              t "let none = (inj () = L) in let some = fun x -> (inj x = R) in case (some 1) {L(x) -> 0 | R(n) -> n + 1}" (ENum 2) TNum
            ],
        TestLabel "different_types" $
          t "let id = fun x -> x in if (id true) then (id 100) else 1" (ENum 100) TNum
      ]

-- More type check
testMoreTypeCheck :: Test
testMoreTypeCheck =
  TestLabel "MoreTypeCheck" $
    TestList
      [ tType "()" TUnit,
        tType "true" TBool,
        tType "false" TBool,
        tType "1" TNum,
        tType "0" TNum,
        tType "1+2" TNum,
        tType "1-2" TNum,
        tType "1*2" TNum,
        tType "1/2" TNum,
        tType "1<2" TBool,
        tType "1>2" TBool,
        tType "1==2" TBool,
        tType "true && false" TBool,
        tType "true || false" TBool,
        tType "if true then 1 else 2" TNum,
        tType "if false then 1 else 2" TNum,
        tType "(fun x -> x) 1" TNum,
        tType "(fun x -> 1) 2" TNum,
        tType "let f = fun x -> x + 1 in f 2" TNum,
        tType "(1, true).L" TNum,
        tType "(1, true).R" TBool,
        tType "case inj 1 = L { L(x) -> x | R(y) -> y }" TNum,
        tType "fix f -> 1" TNum,
        tType "let f = fun x -> fun y -> x y in let g = f (fun x -> x) in g 1" TNum,
        tType "(fun z -> ((fun x -> fun y -> y x) z (fun x -> x))) 100" TNum,
        tTypeError "x",
        TestLabel "free_var" $ TestCase $ do
          case checkType "let id = fun x -> x in id" of
            Left err -> assertFailure err
            Right (TForall a (TFn arg ret)) -> do
              let showA = show a
              assertBool "arg is TVar a" $ case arg of TVar (Variable v) -> v == showA; _ -> False
              assertBool "ret is TVar a" $ case ret of TVar (Variable v) -> v == showA; _ -> False
            Right ty -> assertFailure $ "Expected forall fn, got " ++ show ty,
        TestLabel "fn_const" $ TestCase $ do
          case checkType "fun x -> true && x" of
            Left err -> assertFailure err
            Right (TFn arg ret) -> assertEqual "fn_const" (TFn TBool TBool) (TFn arg ret)
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty,
        TestLabel "fn_nested" $ TestCase $ do
          case checkType "let f = fun x -> fun y -> x + y in f" of
            Left err -> assertFailure err
            Right (TForall _ (TFn arg (TFn arg2 ret2))) ->
              assertEqual "fn_nested" (TFn TNum (TFn TNum TNum)) (TFn arg (TFn arg2 ret2))
            Right (TFn arg (TFn arg2 ret2)) ->
              assertEqual "fn_nested" (TFn TNum (TFn TNum TNum)) (TFn arg (TFn arg2 ret2))
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty,
        TestLabel "fn_passing_fn" $ TestCase $ do
          case checkType "fun f -> (f true) < 2" of
            Left err -> assertFailure err
            Right (TFn (TFn arg2 ret2) TBool) ->
              assertEqual "fn_passing_fn arg" TBool arg2 >> assertEqual "fn_passing_fn ret" TNum ret2
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty,
        TestLabel "pair_type" $ TestCase $ do
          case checkType "(1, true)" of
            Left err -> assertFailure err
            Right (TProduct l r) -> assertEqual "pair" (TProduct TNum TBool) (TProduct l r)
            Right ty -> assertFailure $ "Expected product, got " ++ show ty,
        TestLabel "inject_left" $ TestCase $ do
          case checkType "inj 1 = L" of
            Left err -> assertFailure err
            Right (TForall _ (TSum l _)) -> assertEqual "inject left" TNum l
            Right (TSum l _) -> assertEqual "inject left" TNum l
            Right ty -> assertFailure $ "Unexpected: " ++ show ty,
        TestLabel "inject_right" $ TestCase $ do
          case checkType "inj true = R" of
            Left err -> assertFailure err
            Right (TForall _ (TSum _ r)) -> assertEqual "inject right" TBool r
            Right (TSum _ r) -> assertEqual "inject right" TBool r
            Right ty -> assertFailure $ "Unexpected: " ++ show ty,
        TestLabel "letrec_type" $ TestCase $ do
          case checkType "letrec f = fun x -> if x == 0 then 0 else (f (x - 1)) + 1 in f" of
            Left err -> assertFailure err
            Right (TFn arg ret) -> assertEqual "letrec_type" (TFn TNum TNum) (TFn arg ret)
            Right ty -> assertFailure $ "Expected fn, got " ++ show ty,
        TestLabel "polymorphism" $ TestCase $ do
          case checkType "let id = fun x -> x in let f = fun y -> y in (id true, f 1)" of
            Left err -> assertFailure err
            Right (TProduct l r) -> assertEqual "poly" (TProduct TBool TNum) (TProduct l r)
            Right ty -> assertFailure $ "Expected product, got " ++ show ty
      ]

-- Type errors
testTypeErrors :: Test
testTypeErrors =
  TestLabel "TypeErrors" $
    TestList
      [ TestLabel "arithmetic" $
          TestList
            [tTypeError "1+()", tTypeError "()-()"],
        TestLabel "conditionals" $
          TestList
            [ tTypeError "true || 1",
              tTypeError "() && true",
              tTypeError "if true then 1 else ()",
              tTypeError "if 0 then 1 else 2",
              tTypeError "1==()",
              tTypeError "(fun x -> x)>1"
            ],
        TestLabel "functions" $
          TestList
            [tTypeError "x", tTypeError "1 ()"],
        TestLabel "adt" $
          TestList
            [ tTypeError "1.L",
              tTypeError "case () {L(l)->l+1|R(r)->3*r}",
              tTypeError "1*(1,2)",
              tTypeError "(inj 1=L)/1",
              tTypeError "1<(2,3)"
            ],
        TestLabel "fixpoints" $ tTypeError "letrec f = 5 in f 1"
      ]

-- Type preservation: type-check result is the same before and after tryStep
testTypePreservation :: Test
testTypePreservation =
  TestLabel "TypePreservation" $
    TestList
      [ TestLabel "arithmetic" $
          TestList
            [ tStep "1+2",
              tStep "1-2",
              tStep "1*2",
              tStep "1/2",
              tStep "(1+2)*(3+4)",
              tStep "(1+2*3)/(4-5)",
              tStep "(1+2)/3"
            ],
        TestLabel "relop" $
          TestList
            [tStep "1<2", tStep "1>2", tStep "1==2"],
        TestLabel "and_or" $
          TestList
            [ tStep "true && false",
              tStep "false || true",
              tStep "true || true",
              tStep "false && false"
            ],
        TestLabel "if" $
          TestList
            [tStep "if true then 1 else 2", tStep "if false then 1 else 2"],
        TestLabel "if_complex" $
          TestList
            [ tStep "if (1 < 2) && (3 == 3) then 4 else 5",
              tStep "(if true then (fun x -> x + 1) else (fun x -> x * 2)) 3",
              tStep "((fun b -> if b then (1, 2) else (3, 4)) true).R"
            ],
        TestLabel "application" $
          TestList
            [ tStep "(fun x -> x) 1",
              tStep "(fun x -> x + 1) 5",
              tStep "(fun x -> (x + 1, x * 2)) 5",
              tStep "(fun f -> f true) (fun x -> x)",
              tStep "(fun p -> (p.L) + (p.R)) (1, 2)",
              tStep "(fun x -> fun y -> x + y) 1",
              tStep "((fun x -> fun y -> x + y) 1) 2"
            ],
        TestLabel "let" $
          TestList
            [ tStep "let x = 1 in x + 2",
              tStep "let x = () in x",
              tStep "let x = 1 + 2 in let y = x + 3 in y + 4",
              tStep "let id = fun x -> x in (id true, id 1)",
              tStep "let f = fun x -> x + 1 in (f 1, f 2)",
              tStep "let pair = (1, true) in (pair.L, pair.R)",
              tStep "let pair = (1, true) in if (pair.L) == 1 then (pair.R) else false"
            ],
        TestLabel "project" $
          TestList
            [ tStep "(1, true).L",
              tStep "(1, 2).R",
              tStep "((1, 2), (3, 4)).L",
              tStep "((1, 2), (3, 4)).R"
            ],
        TestLabel "project_if" $
          TestList
            [tStep "(if true then (1, 2) else (3, 4)).L"],
        TestLabel "case" $
          TestList
            [ tStep "case (inj 1 = L) {L(l) -> l | R(r) -> 3 * r}",
              tStep "case (inj (1, 2) = L) {L(p) -> (p.L) | R(q) -> 0}",
              tStep "let x = (inj 1 = L) in case x {L(n) -> n + 1 | R(n) -> 3 * n}"
            ],
        TestLabel "fix" $
          TestList
            [ tStep "fix f -> (fun x -> x + 1)",
              tStep "(fix f -> (fun x -> x + 1)) 5"
            ],
        TestLabel "and_or_step" $
          TestList
            [ tStep "true && false",
              tStep "false || true",
              tStep "true && (1 == 1)",
              tStep "false || (1 == 2)"
            ],
        TestLabel "project_both" $
          TestList
            [ tStep "(1, 2).L",
              tStep "(1, 2).R"
            ],
        TestLabel "case_both" $
          TestList
            [ tStep "case (inj 1 = L) {L(x) -> x | R(y) -> 3 * y}",
              tStep "case (inj 1 = R) {L(y) -> 3 | R(x) -> x * 2}"
            ],
        TestLabel "subst_and_or" $
          TestList
            [ tStep "let x = true in x && (2 == 2)",
              tStep "let x = false in x || (1 == 2)",
              tStep "(fun x -> x && true) true",
              tStep "(fun x -> x || false) false"
            ],
        TestLabel "subst_all" $
          TestList
            [ tStep "let x = 1 / 2 in x + 1",
              tStep "let x = (1, true).L in x",
              tStep "let x = (1, true).R in x"
            ]
      ]

testFlags :: Test
testFlags =
  TestLabel "Flags" $
    TestList
      [ TestLabel "formatAst" $
          TestList
            [ tFormatAst "1+2" Full Nothing "(1 + 2)",
              tFormatAst "1+2" Simplified Nothing "(1 + 2)",
              tFormatAst "1+2" DeBruijn Nothing "(1 + 2)"
            ],
        TestLabel "formatType" $
          TestList
            [ tFormatType "1" Full "num",
              tFormatType "1" Simplified "num",
              tFormatType "1" DeBruijn "num",
              tFormatType "1" Graphviz "",
              tFormatType "true" Full "bool",
              tFormatType "true" Simplified "bool",
              tFormatType "true" DeBruijn "bool",
              tFormatType "true" Graphviz ""
            ]
      ]

testDotGen :: Test
testDotGen =
  TestLabel "DotGen" $
    TestList
      [ tFormatAst
          "1"
          Graphviz
          Nothing
          "digraph {\n\t0 [shape=point, width=0.1];\n\t1 [shape=point, width=0.1, color=\"red\"];\n\t0 -> 1 [label=\"1\", arrowhead=none, color=\"red\", fontcolor=\"red\"];\n}",
        tFormatAst
          "1"
          Graphviz
          (Just "test")
          "subgraph test {\n\t0 [shape=point, width=0.1];\n\t1 [shape=point, width=0.1, color=\"red\"];\n\t0 -> 1 [label=\"1\", arrowhead=none, color=\"red\", fontcolor=\"red\"];\n}",
        tFormatAst
          "true && false"
          Graphviz
          Nothing
          "digraph {\n\t0 [shape=point, width=0.1];\n\t1 [shape=point, width=0.1, color=\"red\"];\n\t0 -> 1 [label=\"&&\", arrowhead=none, color=\"red\", fontcolor=\"red\"];\n\t2 [shape=point, width=0.1, color=\"red\"];\n\t1 -> 2 [label=\"true\", arrowhead=none, color=\"red\", fontcolor=\"red\"];\n\t3 [shape=point, width=0.1, color=\"red\"];\n\t1 -> 3 [label=\"false\", arrowhead=none, color=\"red\", fontcolor=\"red\"];\n}",
        tFormatAstContent "1+2" "+",
        tFormatAstContent "2*3" "*",
        tFormatAstContent "if true then 1 else 2" "if",
        tFormatAstContent "1<2" "<",
        tFormatAstContent "true || false" "||",
        tFormatAstContent "(1,true)" "pair",
        tFormatAstContent "()" "()",
        tFormatAstContent "(fun x -> x) 1" "app",
        tFormatAstContent "(1,2).L" "P_left",
        tFormatAstContent "inj 1 = L" "I_left",
        tFormatAstContent "let x = 1 in x" "let",
        tFormatAstContent "fix f -> f" "fix"
      ]

tFormatAstContent :: String -> String -> Test
tFormatAstContent s label = TestCase $
    case parse s of
        Left err -> assertFailure $ "Parse error: " ++ err
        Right e -> do
            let result = formatAst e Graphviz Nothing
            assertBool ("Graphviz output for " ++ s ++ " should contain " ++ label)
                       (label `isInfixOf` result)
            assertBool "Graphviz output should start with digraph"
                       ("digraph" `isPrefixOf` result)

testUnionFind :: Test
testUnionFind =
  TestLabel "UnionFind" $
    TestList
      [ TestLabel "connected" $ TestCase $ do
          let vs = map Variable ["a", "b", "c"]
          let uf = mkUnionFind vs
          result <- case connected uf (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          assertBool "a and b not connected initially" (not result),
        TestLabel "union_connected" $ TestCase $ do
          let vs = map Variable ["a", "b", "c"]
          let uf = mkUnionFind vs
          (uf', _) <- case union uf (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          result <- case connected uf' (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          assertBool "a and b connected after union" result,
        TestLabel "find_not_found" $ TestCase $ do
          let vs = map Variable ["a"]
          let uf = mkUnionFind vs
          case find uf (Variable "z") of
            Left _ -> return ()
            Right _ -> assertFailure "Expected error",
        TestLabel "union_same" $ TestCase $ do
          let vs = map Variable ["a", "b"]
          let uf = mkUnionFind vs
          (_, r) <- case union uf (Variable "a") (Variable "a") of
            Left err -> assertFailure err
            Right r -> return r
          assertEqual "union same" (Variable "a") r,
        TestLabel "union_eq_rank" $ TestCase $ do
          let vs = map Variable ["a", "b"]
          let uf = mkUnionFind vs
          (uf', _) <- case union uf (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          rootA <- case find uf' (Variable "a") of Left _ -> assertFailure "find"; Right r -> return r
          rootB <- case find uf' (Variable "b") of Left _ -> assertFailure "find"; Right r -> return r
          assertEqual "both in same set" rootA rootB,
        TestLabel "find_path_compression" $ TestCase $ do
          let vs = map Variable ["a", "b", "c"]
          let uf = mkUnionFind vs
          (uf1, _) <- case union uf (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          (uf2, _) <- case union uf1 (Variable "b") (Variable "c") of
            Left err -> assertFailure err
            Right r -> return r
          _ <- case find uf2 (Variable "a") of Left err -> assertFailure err; Right r -> return r
          _ <- case find uf2 (Variable "c") of Left err -> assertFailure err; Right r -> return r
          conn <- case connected uf2 (Variable "a") (Variable "c") of
            Left err -> assertFailure err
            Right r -> return r
          assertBool "a and c connected" conn,
        TestLabel "find_rank_lt" $ TestCase $ do
          let vs = map Variable ["a", "b"]
          let uf0 = mkUnionFind vs
          let uf1 = uf0 {rank = Map.insert (Variable "b") 1 (rank uf0)}
          (_, r) <- case union uf1 (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          assertEqual "rank LT attaches to higher" (Variable "b") r,
        TestLabel "find_path_compression_depth" $ TestCase $ do
          let vs = map Variable ["a", "b", "c"]
          let uf = mkUnionFind vs
          (uf1, _) <- case union uf (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          (uf2, _) <- case union uf1 (Variable "a") (Variable "c") of
            Left err -> assertFailure err
            Right r -> return r
          _ <- case find uf2 (Variable "c") of
            Left err -> assertFailure err
            Right r -> return r
          return (),
        TestLabel "find_with_compression" $ TestCase $ do
          let vs = map Variable ["a", "b", "c", "d", "e"]
          let uf = mkUnionFind vs
          (uf1, _) <- case union uf (Variable "d") (Variable "e") of
            Left err -> assertFailure err
            Right r -> return r
          (uf2, _) <- case union uf1 (Variable "a") (Variable "b") of
            Left err -> assertFailure err
            Right r -> return r
          (uf3, _) <- case union uf2 (Variable "a") (Variable "c") of
            Left err -> assertFailure err
            Right r -> return r
          -- now rank a = 2, rank d = 1
          -- union a (rank 2) with d (rank 1) -> GT: d attaches to a
          (uf4, _) <- case union uf3 (Variable "a") (Variable "d") of
            Left err -> assertFailure err
            Right r -> return r
          -- now find e -> should trigger path compression: e -> d -> a
          _ <- case find uf4 (Variable "e") of
            Left err -> assertFailure err
            Right r -> return r
          return ()
      ]

testTryStep :: Test
testTryStep =
  TestLabel "TryStep" $
    TestList
      [ TestLabel "EDeBruijn" $
          TestCase $
            case tryStep (EDeBruijn 0) of
              Val -> return ()
              _ -> assertFailure "EDeBruijn should be Val",
        TestLabel "ELam" $
          TestCase $
            case tryStep (ELam (Variable "x") Nothing (ENum 1)) of
              Val -> return ()
              _ -> assertFailure "ELam should be Val",
        TestLabel "EPair" $
          TestCase $
            case tryStep (EPair (ENum 1) (ENum 2)) of
              Val -> return ()
              _ -> assertFailure "EPair should be Val",
        TestLabel "EInject" $
          TestCase $
            case tryStep (EInject (ENum 1) L) of
              Val -> return ()
              _ -> assertFailure "EInject should be Val",
        TestLabel "deBruijnSubst_outside_ref" $ TestCase $ do
          let e = EApp (ELam (Variable "_") Nothing (EApp (ELam (Variable "_") Nothing (EDeBruijn 1)) (ENum 1))) (ENum 2)
          case tryStep e of
            Step e' -> assertEqual "outer app step" (EApp (ELam (Variable "_") Nothing (ENum 2)) (ENum 1)) e'
            _ -> assertFailure "Expected Step",
        TestLabel "parseError" $ tParseError "let in",
        TestLabel "keyword_as_var" $ tParseError "fun let -> x"
      ]

testShowInstances :: Test
testShowInstances =
  TestLabel "ShowInstances" $
    TestList
      [ tShow "1" "1",
        tShow "true" "true",
        tShow "false" "false",
        tShow "()" "()",
        tShow "1+2" "(1 + 2)",
        tShow "1-2" "(1 - 2)",
        tShow "1*2" "(1 * 2)",
        tShow "1/2" "(1 / 2)",
        tShow "1==2" "(1 = 2)",
        tShow "1<2" "(1 < 2)",
        tShow "1>2" "(1 > 2)",
        tShow "true && false" "(true && false)",
        tShow "true || false" "(true || false)",
        tShow "(1,true)" "(1 , true)",
        tShow "fun x -> x" "(λ x -> x)",
        tShow "if true then 1 else 2" "(if true then 1 else 2)",
        tShow "inj 1=L" "1",
        tShow "let x = 1 in x" "(let x = 1 in x)",
        tShow "fix f -> f" "(fix f -> f)",
        tShow "case inj 1=L {L(x)->x|R(y)->y}" "(case 1 of L(x) -> x | R(y) -> y)",
        tShowType "1" "num",
        tShowType "true" "bool",
        tShowType "()" "()",
        tShowType "1+2" "num",
        tShowType "1<2" "bool",
        TestLabel "edebruijn" $ TestCase $ do
          assertEqual "show EDeBruijn" "<5>" (show (EDeBruijn 5)),
        TestLabel "project_pair" $ TestCase $ do
          assertEqual "project L on pair" "1" (show (EProject (EPair (ENum 1) (ENum 2)) L))
          assertEqual "project R on pair" "2" (show (EProject (EPair (ENum 1) (ENum 2)) R)),
        TestLabel "project_non_pair" $ TestCase $ do
          assertEqual "project on var" "x.L" (show (EProject (EVar (Variable "x")) L)),
        TestLabel "eapp_show" $ TestCase $ do
          let e = EApp (ELam (Variable "x") Nothing (EVar (Variable "x"))) (ENum 1)
          assertEqual "show EApp" "((λ x -> x) 1)" (show e),
        TestLabel "inject_show" $ TestCase $ do
          assertEqual "inject" "1" (show (EInject (ENum 1) L)),
        TestLabel "eval_type_show" $ TestCase $ do
          assertEqual "TNum" "num" (show (TNum :: Type))
          assertEqual "TBool" "bool" (show (TBool :: Type))
          assertEqual "TUnit" "()" (show (TUnit :: Type))
          assertEqual "TVar" "x" (show (TVar (Variable "x") :: Type))
          assertEqual "TFn" "(num → bool)" (show (TFn TNum TBool))
          assertEqual "TProduct" "num * bool" (show (TProduct TNum TBool))
          assertEqual "TSum" "num + bool" (show (TSum TNum TBool))
          assertEqual "TForall" "∀ x . num" (show (TForall (Variable "x") TNum)),
        TestLabel "op_show" $ TestCase $ do
          assertEqual "Add" "+" (show Add)
          assertEqual "Sub" "-" (show Sub)
          assertEqual "Mul" "*" (show Mul)
          assertEqual "Div" "/" (show Div)
          assertEqual "Lt" "<" (show Lt)
          assertEqual "Gt" ">" (show Gt)
          assertEqual "Eq" "=" (show Eq)
          assertEqual "Direction L" "L" (show L)
          assertEqual "Direction R" "R" (show R),
        TestLabel "eunit" $ TestCase $ do
          assertEqual "EUnit" "()" (show EUnit),
        TestLabel "free_var_in_ast" $ TestCase $ do
          assertEqual "free var not bound" "(λ x -> (x y))" (show (ELam (Variable "x") Nothing (EApp (EVar (Variable "x")) (EVar (Variable "y"))))),
        TestLabel "debruijn_output_type" $ TestCase $ do
          case checkType "let id = fun x -> x in id" of
            Left err -> assertFailure err
            Right ty -> do
              let db = formatType ty DeBruijn
              assertBool "DeBruijn type contains forall" ("∀ _" `isPrefixOf` db)
      ]

testTypeCheckUtil :: Test
testTypeCheckUtil =
  TestLabel "TypeCheckUtil" $
    TestList
      [ TestLabel "debruijn_out_of_bounds" $
          TestCase $
            case typeCheck (EDeBruijn 5) of
              Left _ -> return ()
              Right ty -> assertFailure $ "Expected error, got " ++ show ty,
        TestLabel "generalize_quantifies_free_vars" $
          TestCase $
            case generalize (TVar (Variable "type_0")) [] of
              Left err -> assertFailure $ "Expected generalize to succeed, got: " ++ err
              Right ty ->
                assertEqual
                  "generalize should quantify free vars"
                  (TForall (Variable "type_0") (TVar (Variable "type_0")))
                  ty,
        TestLabel "check_free_vars_remain" $
          TestCase $
            case checkType "let id = fun x -> x in id" of
              Right (TForall _ _) -> return ()
              _ -> assertFailure "Expected forall type",
        TestLabel "unify_tunit" $ TestCase $ do
          let constraint = Constraint TUnit TUnit "" ""
          case unification [constraint] of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "unify_var_var_just_nothing" $ TestCase $ do
          let c1 = Constraint (TVar (Variable "type_1")) TNum "" ""
          let c2 = Constraint (TVar (Variable "type_1")) (TVar (Variable "type_0")) "" ""
          case unification [c1, c2] of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "unify_var_var_nothing_just" $ TestCase $ do
          let c1 = Constraint (TVar (Variable "type_0")) TNum "" ""
          let c2 = Constraint (TVar (Variable "type_1")) (TVar (Variable "type_0")) "" ""
          case unification [c1, c2] of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "unify_var_var_both_just" $ TestCase $ do
          let c1 = Constraint (TVar (Variable "type_0")) TNum "" ""
          let c2 = Constraint (TVar (Variable "type_1")) TBool "" ""
          let c3 = Constraint (TVar (Variable "type_0")) (TVar (Variable "type_1")) "" ""
          case unification [c1, c2, c3] of
            Left _ -> return ()
            Right _ -> assertFailure "Expected unification failure",
        TestLabel "unify_var_type_already_mapped" $ TestCase $ do
          let c1 = Constraint (TVar (Variable "type_0")) TNum "" ""
          let c2 = Constraint (TVar (Variable "type_0")) TBool "" ""
          case unification [c1, c2] of
            Left _ -> return ()
            Right _ -> assertFailure "Expected unification failure",
        TestLabel "unify_tfn" $ TestCase $ do
          let c = Constraint (TFn TNum TNum) (TFn TNum TNum) "" ""
          case unification [c] of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "unify_tproduct" $ TestCase $ do
          let c = Constraint (TProduct TNum TBool) (TProduct TNum TBool) "" ""
          case unification [c] of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "unify_tsum" $ TestCase $ do
          let c = Constraint (TSum TNum TBool) (TSum TNum TBool) "" ""
          case unification [c] of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "unify_var_occurs_check" $ TestCase $ do
          let c = Constraint (TVar (Variable "type_0")) (TFn (TVar (Variable "type_0")) TNum) "" ""
          case unification [c] of
            Left _ -> return ()
            Right _ -> assertFailure "Expected occurs check failure",
        TestLabel "typecheck_free_vars_remain" $ TestCase $ do
          case typeCheck (EApp (EDeBruijn 1) (ENum 1)) of
            Left _ -> return ()
            Right _ -> assertFailure "Expected type error for free variables"
      ]

testParseErrors :: Test
testParseErrors =
  TestLabel "ParseErrors" $
    TestList
      [ tParseError "let in",
        tParseError "fun let -> x",
        TestLabel "invalid_expr" $
          TestCase $
            case parse "(@" of
              Left _ -> return ()
              Right e -> assertFailure $ "Expected parse error, got " ++ show e
      ]

-- Type annotations
testAnnotations :: Test
testAnnotations =
  TestLabel "Annotations" $
    TestList
      [ TestLabel "lam_simple" $
          TestList
            [ tType "fun (x : num) -> x + 1" (TFn TNum TNum)
            ],
        TestLabel "lam_parse" $ TestCase $ do
          case parse "fun (x : num) -> x + 1" of
            Left err -> assertFailure err
            Right e -> assertEqual "parse lam annotation" (ELam (Variable "x") (Just TNum) (EAddop Add (EVar (Variable "x")) (ENum 1))) e,
        TestLabel "lam_parse_unannotated" $ TestCase $ do
          case parse "fun x -> x" of
            Left err -> assertFailure err
            Right e -> assertEqual "parse lam no annotation" (ELam (Variable "x") Nothing (EVar (Variable "x"))) e,
        TestLabel "let_parse" $ TestCase $ do
          case parse "let x : num = 1 in x + 2" of
            Left err -> assertFailure err
            Right e -> assertEqual "parse let annotation" (ELet (Variable "x") (Just TNum) (ENum 1) (EAddop Add (EVar (Variable "x")) (ENum 2))) e,
        TestLabel "let_parse_unannotated" $ TestCase $ do
          case parse "let x = 1 in x" of
            Left err -> assertFailure err
            Right e -> assertEqual "parse let no annotation" (ELet (Variable "x") Nothing (ENum 1) (EVar (Variable "x"))) e,
        TestLabel "lam_typecheck" $
          TestList
            [ tType "fun (x : num) -> x + 1" (TFn TNum TNum),
              tType "fun (x : num) -> x" (TFn TNum TNum),
              tType "fun (x : bool) -> x" (TFn TBool TBool),
              tType "fun (x : num) -> fun (y : num) -> x + y" (TFn TNum (TFn TNum TNum))
            ],
        TestLabel "let_typecheck" $
          TestList
            [ tType "let x : num = 1 in x" TNum,
              tType "let x : num = 1 in x + 2" TNum,
              tType "let id : num -> num = fun x -> x in id 1" TNum,
              tType "let id : num -> num = fun x -> x in id 1" TNum
            ],
        TestLabel "lam_eval" $
          TestList
            [ t "(fun (x : num) -> x + 1) 5" (ENum 6) TNum,
              t "let f = fun (x : num) -> x + 1 in f 5" (ENum 6) TNum,
              t "(fun (f : num -> num) -> f 5) (fun x -> x + 1)" (ENum 6) TNum
            ],
        TestLabel "let_eval" $
          TestList
            [ t "let x : num = 3 in x + 2" (ENum 5) TNum,
              t "let id : num -> num = fun (x : num) -> x in id 5" (ENum 5) TNum
            ],
        TestLabel "complex_types" $
          TestList
            [ tType "fun (f : num -> num) -> f 0" (TFn (TFn TNum TNum) TNum),
              tType "let p : num * bool = (1, true) in p.L" TNum,
              tType "let p : num * bool = (1, true) in p.R" TBool,
              tType "fun (x : num * bool) -> x" (TFn (TProduct TNum TBool) (TProduct TNum TBool)),
              tType "let x : () = () in x" TUnit
            ],
        TestLabel "type_errors" $
          TestList
            [ tTypeError "fun (x : bool) -> x + 1",
              tTypeError "fun (x : num) -> x && true",
              tTypeError "let x : num = true in x",
              tTypeError "let x : bool = 1 in x",
              tTypeError "fun (x : num -> bool) -> x + 1"
            ],
        TestLabel "type_preservation" $
          TestList
            [ tStep "let x : num = 1 in x + 2",
              tStep "let id : num -> num = fun (x : num) -> x in id 5",
              tStep "(fun (x : num) -> x + 1) 5",
              tStep "let x : num = 1 + 2 in x * 3"
            ],
        TestLabel "show" $
          TestList
            [ tShow "fun (x : num) -> x" "(λ x : num -> x)",
              tShow "let x : num = 1 in x" "(let x : num = 1 in x)",
              tShow "fun (f : num -> bool) -> f 0" "(λ f : (num → bool) -> (f 0))"
            ],
        TestLabel "let_poly_with_annotation" $
          TestList
            [ tType "let id : num -> num = fun x -> x in id" (TFn TNum TNum),
              tType "let f : (num * bool) -> num = fun p -> p.L in f" (TFn (TProduct TNum TBool) TNum)
            ],
        TestLabel "parenthesized_type" $ TestCase $ do
          case parse "fun (x : (num -> bool) * num) -> x" of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "sum_annotation" $ TestCase $ do
          case parse "fun (x : num + bool) -> x" of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "type_var_annotation" $ TestCase $ do
          case parse "fun (x : a) -> x" of
            Left err -> assertFailure err
            Right _ -> return (),
        TestLabel "type_var_debruijn" $ TestCase $ do
          case parse "fun (x : a) -> x" of
            Left err -> assertFailure err
            Right e -> do
              let db = toDebruijn e
              assertEqual "debruijn preserves type var"
                (ELam (Variable "_") (Just (TVar (Variable "a"))) (EDeBruijn 0))
                db,
        TestLabel "annotated_type_preservation" $
          TestList
            [ tStep "let x : num = 1 in x + 2",
              tStep "let x : num = 1 + 2 in x * 3",
              tStep "(fun (x : num) -> x + 1) 5",
              tStep "let f : num -> num = fun (x : num) -> x in f 5",
              tStep "let x : num * bool = (1, true) in x.L",
              tStep "let x : num * bool = (1, true) in x.R"
            ],
        TestLabel "show_complex" $
          TestList
            [ tShow "fun (x : num * bool) -> x" "(λ x : num * bool -> x)",
              tShow "fun (x : num + bool) -> x" "(λ x : num + bool -> x)",
              tShow "fun (x : (num -> bool) * num) -> x" "(λ x : (num → bool) * num -> x)"
            ],
        TestLabel "annotation_parse_errors" $
          TestList
            [ tParseError "fun (: num) -> x",
              tParseError "fun (x :) -> x",
              tParseError "fun (x : -> num) -> x"
            ],
        TestLabel "forall_annotations" $
          TestList
            [ tType "let f : ∀ a . a -> a = fun x -> x in f 1" TNum,
              tType "let f : ∀ a . a -> a = fun x -> x in f true" TBool,
              tType "let f : ∀ a . a -> a = fun x -> x in (f 1, f true)" (TProduct TNum TBool),
              tType "let f : ∀ a . a -> bool = fun x -> true in f 1" TBool,
              tTypeError "let f : ∀ a . a -> a = 1 in f 1",
              tTypeError "let f : ∀ a . a -> bool = fun x -> x in f 1",
              t "let f : ∀ a . a -> a = fun x -> x in f 1" (ENum 1) TNum,
              tStep "let f : ∀ a . a -> a = fun x -> x in f 1",
              tStep "let f : ∀ a . a -> a = fun x -> x in (f 1, f true)",
              tStep "let f : ∀ a . a -> bool = fun x -> true in f 1",
              tShow "let f : ∀ a . a -> a = fun x -> x in f 1" "(let f : ∀ a . (a → a) = (λ x -> x) in (f 1))",
              tParseError "let f : ∀ = fun x -> x in f 1",
              tParseError "let f : ∀ a = fun x -> x in f 1"
            ]
      ]
