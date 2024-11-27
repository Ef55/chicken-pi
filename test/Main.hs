module Main where

import Arbitrary (prop_roundtrip)
import Control.Monad.Except
import Data.List (intercalate)
import Environment
import Modules
import PrettyPrint
import Syntax
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.ParserCombinators.Parsec.Error
import Text.PrettyPrint.HughesPJ (render)
import TypeCheck

main :: IO ()
main = do
  let dataTests = testGroup "Data" (testFile ["pi/Data"] <$> ["Unit", "Bool", "Nat"])
  defaultMain $
    testGroup
      "Tests"
      [ -- QC.testProperty "PP-Parsing round trip" prop_roundtrip,
        dataTests
      ]

exitWith :: Either a b -> (a -> IO b) -> IO b
exitWith (Left a) f = f a
exitWith (Right b) f = return b

-- | Type check the given file
testFile :: [String] -> String -> TestTree
testFile path name = testCase name $ do
  v <- runExceptT (getModules path name)
  val <- v `exitWith` (\b -> assertFailure $ "Parse error: " ++ render (disp b))
  case runTcMonad emptyEnv (tcModules val) of
    (Left err, _) -> assertFailure $ "Type error:" ++ render (disp err)
    (_, logs@(_ : _)) -> assertFailure $ "Warnings were produced:" ++ intercalate "\n" logs
    (Right defs, _) -> return ()