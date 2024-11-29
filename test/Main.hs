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

main :: IO ()
main = do
  let dataExamples = testGroup "Examples: Data" (tcFile ["pi/Data"] <$> ["Unit", "Bool", "Nat", "Pos"])
  let dataTests = testGroup "Data" (tcFile ["test/Data"] <$> ["Dependent"])
  let matchingTests = testGroup "Matching" (tcFile ["test/Matching"] <$> ["Subst", "Eval", "Wildcard"])
  let failingTests =
        testGroup
          "Failing"
          [ failingFile "Non exhaustive pattern matching" ["test/Failing"] "NonExhaustive" "pattern matching.*2 branches.*3 constructors",
            failingFile "Unordered pattern matching" ["test/Failing"] "UnorderedPatterns" "Three.*Two was expected",
            failingFile "Wildcard is not a variable" ["test/Failing"] "WildcardVar" "expecting a variable"
          ]
  defaultMain $
    testGroup
      "Tests"
      [ -- QC.testProperty "PP-Parsing round trip" prop_roundtrip,
        dataExamples,
        dataTests,
        matchingTests,
        failingTests
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
failingFile expl path name expected = tester name path name $ \case
  TestSuccess _ logs@(_ : _) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" logs
  TestSuccess r [] -> assertFailure $ "File did not fail with expected error: " ++ render (disp expected)
  ParsingFailure err -> checkErr (show err)
  TypingFailure (Err _ err) -> checkErr (render err)
  where
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
