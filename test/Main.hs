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

--------------------------------------------------------------------------------
-- Definition of tests to run
--------------------------------------------------------------------------------

anyErr :: String
anyErr = ""

unknownErr :: String
unknownErr = "\\?\\?\\?"

tests :: TestTree
tests =
  let dataTests =
        testGroup "Data" $
          positiveTests "test/Data" ["Dependent", "MultiParams", "ContraPos"]
            ++ negativeTests
              "test/Data"
              [ ("Constructors must be for the type being defined", "DefinesOtherType", "C1.*has type D0.*should be constructor for D1"),
                ("Constructors must fully apply the type being defined", "NotFullyApplied", "fully applied?"),
                ("Contradiction requires different constructors", "ContraNeg", "same constructor"),
                ("Inner contradiction (unsupported)", "InnerContra", "same constructor")
              ]

      matchingTests =
        testGroup
          "Matching"
          $ positiveTests "test/Matching" ["Subst", "Eval", "Wildcard"]
            ++ negativeTests
              "test/Matching"
              [ ("Type mentioned in return clause must match", "WrongInName", "'in' clause.*D1.*should be.*D0")
              ]

      universesTests =
        testGroup
          "Universes"
          $ positiveTests "test/Universes" ["Hierarchy", "ProofErasability", "SingletonElim", "SubsingletonElim"]
            ++ negativeTests
              "test/Universes"
              [ ("'Type 3' is not a 'Type 1'", "InvalidHierarchy1", "Universe level mismatch:.*Type 4.*where.*Type 1.*expected"),
                ("Prop cannot be eliminated into set", "PropElim", "ev.*Prop.*cannot be eliminated into.*Set1.*Set"),
                ("Set is not impredicative", "SetNotImpred", "Type 1.*where.*Set"),
                ("Polymorphic identity is not in Set", "PolymorphicIdentity", "Type 1.*where.*Set")
              ]

      positivityTests =
        testGroup
          "Positivity"
          $ negativeTests
            "test/Positivity"
            [ ("Cannot be argument of argument", "ArgOfArg", "T is currently being defined.*left side.*T -> T"),
              ("Type being defined cannot be used non-uniformly", "SelfNonUniform", "T is currently being defined.*as an argument.*NU T"),
              ("Constructors are parametric on parameters", "ParamNotIndex", "first 2 argument.*should be P Q.*found t0 t1")
            ]

      fixpointTests =
        testGroup "Fixpoint" $
          negativeTests
            "test/Fix"
            [ ("Straight recursion is disallowed", "Straight", "recursive.*u.*structurally smaller.*u"),
              ("Constant recursion is disallowed", "Constant", "recursive.*unit.*structurally smaller.*u"),
              ("Recursion on non-recursive component is disallowed", "NonRecursiveComponent", "recursive.*h.*structurally smaller.*x")
            ]

      failingTests =
        testGroup
          "Failing"
          $ negativeTests
            "test/Failing"
            [ ("Non exhaustive pattern matching", "NonExhaustive", "pattern matching.*2 branches.*3 constructors"),
              ("Unordered pattern matching", "UnorderedPatterns", "Three.*Two was expected"),
              ("Wildcard is not a variable", "WildcardVar", "expecting a variable"),
              ("Missing variable in pattern", "InvalidPattern1", "Instantiation of constructor One.*u0 u1"), -- "too few variables.*\\(_:Unit\\)"
              ("Extra variable in pattern", "InvalidPattern2", "Instantiation of constructor One.*u0 u1 u3 u4"), -- "too many variables.*u4.*unused"
              ("Dependent wildcards must not be confused", "DependentWildcardConfusion", anyErr)
            ]
   in testGroup
        "Tests"
        [ dataTests,
          matchingTests,
          positivityTests,
          fixpointTests,
          universesTests,
          failingTests
        ]

examples :: TestTree
examples =
  let dataExamples = testGroup "Data" (positiveTests "pi/Data" ["Void", "Unit", "Fun", "Bool", "Nat", "Pos", "Maybe", "List", "Sigma", "Fin", "Vect", "HList", "SumBool"])
      logicExamples = testGroup "Logic" $ positiveTests "pi/Logic" ["Logic", "Eq", "Classical"]
      otherExamples = testGroup "Examples" $ positiveTests "pi/Examples" ["PHOAS", "Contra"]
   in testGroup
        "Examples"
        [ dataExamples,
          logicExamples,
          otherExamples
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

--------------------------------------------------------------------------------
-- Helpers for tests definition
--------------------------------------------------------------------------------

standardLibrary :: [String]
standardLibrary = ["pi/Data", "pi/Logic"]

positiveTests :: String -> [String] -> [TestTree]
positiveTests path tests = tcFile [path] <$> tests

negativeTests :: String -> [(String, String, String)] -> [TestTree]
negativeTests path ls =
  (\(name, fileName, err) -> failingFile name [path] fileName err) <$> ls

--------------------------------------------------------------------------------
-- Testing functions
--------------------------------------------------------------------------------

data Result
  = ParsingFailure ParseError
  | TypingFailure Err
  | TestSuccess [Module] [String]

tester :: String -> [String] -> String -> (Result -> Assertion) -> TestTree
tester testName path fileName k = testCase testName $ do
  v <- runExceptT (getModules (path ++ standardLibrary) fileName)
  case v of
    Left b -> k $ ParsingFailure b
    Right val -> case runTcMonad emptyEnv (tcModules val) of
      (Left err, _) -> k $ TypingFailure err
      (Right res, logs) -> k $ TestSuccess res logs

-- | Type check the given file
tcFile :: [String] -> String -> TestTree
tcFile path name = tester (name ++ " [✔]") path name $ \case
  ParsingFailure err -> assertFailure $ "Parsing error:" ++ render (disp err)
  TypingFailure err -> assertFailure $ "Type error:" ++ render (disp err)
  TestSuccess _ logs@(_ : _) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" logs
  TestSuccess r [] -> return ()

-- | Check that processing of a file fails (parsing or type error)
failingFile :: String -> [String] -> String -> String -> TestTree
failingFile expl path name expectedRaw = tester (expl ++ " [✘]") path name $ \case
  TestSuccess _ logs@(_ : _) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" logs
  TestSuccess r [] -> assertFailure "File did not fail."
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
