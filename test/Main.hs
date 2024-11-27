{-# LANGUAGE LambdaCase #-}

module Main where

import Arbitrary (prop_roundtrip)
import Control.Monad.Except
import Data.List (intercalate)
import Data.Maybe (isJust)
import Environment
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

main :: IO ()
main = do
  let dataTests = testGroup "Data" (tcFile ["pi/Data"] <$> ["Unit", "Bool", "Nat"])
  let failingTests =
        testGroup
          "Failing"
          [ failingFile "Non exhaustive pattern matching" ["pi/Failing"] "NonExhaustive" "pattern matching.*2 branches.*3 constructors"
          ]
  defaultMain $
    testGroup
      "Tests"
      [ -- QC.testProperty "PP-Parsing round trip" prop_roundtrip,
        dataTests,
        failingTests
      ]

exitWith :: Either a b -> (a -> IO b) -> IO b
exitWith (Left a) f = f a
exitWith (Right b) f = return b

tester :: String -> [String] -> String -> ((Either Err [Module], [String]) -> Assertion) -> TestTree
tester testName path fileName k = testCase testName $ do
  v <- runExceptT (getModules path fileName)
  val <- v `exitWith` (\b -> assertFailure $ "Parse error: " ++ render (disp b))
  k $ runTcMonad emptyEnv (tcModules val)

disallowWarnings :: (Either Err [Module] -> Assertion) -> (Either Err [Module], [String]) -> Assertion
disallowWarnings k = \case
  (_, logs@(_ : _)) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" logs
  (res, _) -> k res

-- | Type check the given file
tcFile :: [String] -> String -> TestTree
tcFile path name = tester name path name $ disallowWarnings $ \case
  Left err -> assertFailure $ "Type error:" ++ render (disp err)
  Right defs -> return ()

failingFile :: String -> [String] -> String -> String -> TestTree
failingFile expl path name expected = tester expl path name $ disallowWarnings $ \case
  Left err@(Err _ msg) ->
    if isJust $ matchRegex (mkRegexWithOpts expected False False) (render msg) -- render (disp err)
      then return ()
      else
        assertFailure $
          "File did not fail with expected error:\nGot\n"
            ++ render (disp err)
            ++ "\nExpected (regex)\n"
            ++ render (disp expected)
  Right defs -> assertFailure $ "File did not fail with expected error: " ++ render (disp expected)