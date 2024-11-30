{-# LANGUAGE LambdaCase #-}

module Main where

import Arbitrary (prop_roundtrip)
import Control.Monad.Except
import Data.List (intercalate)
import Data.Maybe (isJust)
import Environment
import Equal qualified
import Modules
import PrettyPrint
import Syntax
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.ParserCombinators.Parsec.Error
import Text.PrettyPrint.HughesPJ (render)
import Text.Regex
import TypeCheck
import Unbound.Generics.LocallyNameless (Embed (Embed), bind, string2Name)

tests :: TestTree
tests =
  let dataTests = testGroup "Data" (tcFile ["test/Data"] <$> ["Dependent"])
      matchingTests = testGroup "Matching" (tcFile ["test/Matching"] <$> ["Subst", "Eval", "Wildcard"])
      positivityTests =
        testGroup
          "Positivity"
          [ failingFile "Cannot be argument of argument" ["test/Positivity"] "ArgOfArg" "T is currently being defined.*left side.*T -> T"
          ]
      failingTests =
        testGroup
          "Failing"
          [ failingFile "Non exhaustive pattern matching" ["test/Failing"] "NonExhaustive" "pattern matching.*2 branches.*3 constructors",
            failingFile "Unordered pattern matching" ["test/Failing"] "UnorderedPatterns" "Three.*Two was expected",
            failingFile "Wildcard is not a variable" ["test/Failing"] "WildcardVar" "expecting a variable",
            failingFile "Missing variable in pattern" ["test/Failing"] "InvalidPattern1" "too few variables.*\\(_:Unit\\)",
            failingFile "Extra variable in pattern" ["test/Failing"] "InvalidPattern2" "too many variables.*u4.*unused",
            failingFile "Dependent wildcard must not be confused" ["test/Failing"] "DependentWildcardConfusion" ""
          ]
   in testGroup
        "Tests"
        [ dataTests,
          matchingTests,
          positivityTests,
          -- universesTests,
          failingTests
        ]

examples :: TestTree
examples =
  let dataExamples = testGroup "Data" (tcFile ["pi/Data"] <$> ["Void", "Unit", "Bool", "Nat", "Pos"])
   in testGroup
        "Examples"
        [ dataExamples
        ]

main :: IO ()
main = do
  defaultMain $
    testGroup
      "All"
      [ -- QC.testProperty "PP-Parsing round trip" prop_roundtrip,
        tests,
        examples
      ]

data Result
  = ParsingFailure ParseError
  | TypingFailure Err
  | TestSuccess [Module] [String]

tester :: String -> [String] -> String -> (Result -> Assertion) -> TestTree
tester testName path fileName k = testCase testName $ do
  v <- runExceptT (getModules path fileName)
  case v of
    Left b -> k $ ParsingFailure b
    Right val -> case runTcMonad emptyEnv (tcModules val) of
      (Left err, _) -> k $ TypingFailure err
      (Right res, logs) -> k $ TestSuccess res logs

-- | Type check the given file
tcFile :: [String] -> String -> TestTree
tcFile path name = tester name path name $ \case
  ParsingFailure err -> assertFailure $ "Parsing error:" ++ render (disp err)
  TypingFailure err -> assertFailure $ "Type error:" ++ render (disp err)
  TestSuccess _ logs@(_ : _) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" logs
  TestSuccess r [] -> return ()

-- | Check that processing of a file fails (parsing or type error)
failingFile :: String -> [String] -> String -> String -> TestTree
failingFile expl path name expectedRaw = tester expl path name $ \case
  TestSuccess _ logs@(_ : _) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" logs
  TestSuccess r [] -> assertFailure $ "File did not fail with expected error: " ++ render (disp expected)
  ParsingFailure err -> checkErr (show err)
  TypingFailure (Err _ err) -> checkErr (render err)
  where
    expected = concatMap (\c -> if c == ' ' then "\\s+" else [c]) expectedRaw

    checkErr :: String -> IO ()
    checkErr msg =
      if isJust $ matchRegex (mkRegexWithOpts expected False False) msg
        then return ()
        else
          assertFailure $
            "File did not fail with expected error:\nGot\n"
              ++ msg
              ++ "\nExpected (regex)\n"
              ++ render (disp expected)
