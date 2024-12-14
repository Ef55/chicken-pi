-- | This module is for testing the parser/pretty printer.
-- We would like to satisfy the following roundtrip property:
--     * if we generate a random AST term and print it, then it should parse back to an alpha-equivalent term
module Arbitrary where

import Data.Set qualified as Set
import Parser (expr, testParser)
import PrettyPrint (Disp (disp), render)
import Syntax
import Test.QuickCheck
  ( Arbitrary (arbitrary),
    Gen,
    elements,
    frequency,
    sized,
  )
import Test.QuickCheck qualified as QC
import Text.Parsec.Error (ParseError)
import Unbound.Generics.LocallyNameless qualified as Unbound

-- | Round trip property: a given term prints then parses to the same term.
prop_roundtrip :: Term -> QC.Property
prop_roundtrip tm =
  let str = render (disp tm)
   in case test_parseExpr str of
        Left _ -> QC.counterexample ("*** Could not parse:\n" ++ str) False
        Right tm' -> QC.counterexample ("*** Round trip failure! Parsing:\n" ++ str ++ "\n*** results in\n" ++ show tm') (Unbound.aeq tm tm')

test_parseExpr :: String -> Either Text.Parsec.Error.ParseError Term
test_parseExpr = testParser expr

-- View random terms
sampleTerms :: IO ()
sampleTerms =
  QC.sample' (arbitrary :: Gen Term)
    >>= mapM_ (putStrLn . render . disp)

---------------------------------------------------------------------------------------------------
-- Generators for the pi-forall expression AST
-- These generation functions and Arbitrary instances are tailored for testing the pretty printer
-- and parser. As a result, they do not generate "unprintable" parts of the AST, such as type annotations
-- and source code positions.

-- * Names

-- | variable names
-- drawn from a small list
genName :: Gen (Unbound.Name a)
genName = Unbound.string2Name <$> elements ["x", "y", "z", "x0", "y0"]

instance Arbitrary (Unbound.Name a) where
  arbitrary = genName

-- * Core language

-- Terms with no subterms
base :: Gen Term
base =
  frequency
    [ (2, TyType <$> arbitrary), -- Generate TyType with arbitrary Level
      (1, return TrustMe),
      (1, return PrintMe),
      (1, return Refl)
    ]

-- Generate a random term
-- In the inner recursion, the bool prevents the generation of TyCon/DataCon applications
-- inside Apps --- we want these terms to be fully saturated.
genTerm :: Int -> Gen Term
genTerm n
  | n <= 1 = base
  | otherwise = go True n
  where
    go b n0 =
      let n' = n0 `div` 2
       in frequency
            [ (1, Var <$> genName),
              (1, genLam n'),
              (1, App <$> go False n' <*> genArg n'),
              (1, genPi n'),
              (1, genLet n'),
              (1, TyEq <$> go True n' <*> go True n'),
              (1, Subst <$> go True n' <*> go True n'),
              (1, Contra <$> go True n'),
              (1, base)
            ]

genLam :: Int -> Gen Term
genLam n = do
  p <- genName
  b <- genTerm n
  return $ Lam (Unbound.bind p b)

genPi :: Int -> Gen Term
genPi n = do
  p <- genName
  tyA <- genTerm n
  tyB <- genTerm n
  return $ TyPi tyA (Unbound.bind p tyB)

genLet :: Int -> Gen Term
genLet n = do
  p <- genName
  rhs <- genTerm n
  b <- genTerm n
  return $ Let rhs (Unbound.bind p b)

genArg :: Int -> Gen Term
genArg n = genTerm (n `div` 2)

genArgs :: Int -> Gen [Term]
genArgs n = genBoundedList 2 (genArg n)

instance Arbitrary Level where
  arbitrary = sized genLevel

genLevel :: Int -> Gen Level
genLevel n
  | n <= 0 =
      frequency
        [ (2, return (LConst 0)),
          (1, return (LConst 1))
        ]
  | otherwise = LConst <$> arbitrarySizedNatural

-- Helper function for natural numbers
arbitrarySizedNatural :: Gen Integer
arbitrarySizedNatural = abs <$> arbitrary

instance Arbitrary Term where
  arbitrary = sized genTerm

  -- when QC finds a counterexample, it tries to shrink it to find a smaller one
  shrink (App tm arg) =
    [tm, arg]
      ++ [App tm' arg | tm' <- QC.shrink tm]
      ++ [App tm arg' | arg' <- QC.shrink arg]
  shrink (Lam bnd) = []
  shrink (TyPi tyA bnd) = [tyA]
  shrink (Let rhs bnd) = [rhs]
  shrink (TyEq a b) = [a, b] ++ [TyEq a' b | a' <- QC.shrink a] ++ [TyEq a b' | b' <- QC.shrink b]
  shrink (Subst a b) = [a, b] ++ [Subst a' b | a' <- QC.shrink a] ++ [Subst a b' | b' <- QC.shrink b]
  shrink (Contra a) = a : [Contra a' | a' <- QC.shrink a]
  shrink _ = []

-------------------------------------------------------

-- * General quickcheck utilities

-- | Only generate lists up to size n
genBoundedList :: Int -> Gen a -> Gen [a]
genBoundedList b g = do
  len <- QC.elements [0 .. b]
  take len <$> QC.infiniteListOf g

-- | Run quickcheck for more than 100 tests
quickCheckN :: (QC.Testable prop) => Int -> prop -> IO ()
quickCheckN n = QC.quickCheckWith $ QC.stdArgs {QC.maxSuccess = n, QC.maxSize = 100}