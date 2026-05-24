module Main where
import Parser
import Test.HUnit

main :: IO Counts
main = runTestTT $ TestList
    [ TestCase $ do
        case parse "fix f -> (fun x -> x + 1)" of
            Left err -> assertFailure $ "Parse error: " ++ err
            Right _ -> return ()
    ]
