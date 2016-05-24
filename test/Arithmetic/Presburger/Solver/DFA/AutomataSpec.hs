{-# LANGUAGE RecordWildCards, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE ViewPatterns                                        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Arithmetic.Presburger.Solver.DFA.AutomataSpec where
import Arithmetic.Presburger.Solver.DFA
import Arithmetic.Presburger.Solver.DFA.Automata

import           Control.Monad             (forM)
import           Data.Hashable             (Hashable)
import qualified Data.HashSet              as HS
import qualified Data.Map                  as M
import           Test.QuickCheck.Instances ()
import           Test.Tasty.Discover

instance (Ord s, Ord c, Eq s, Hashable s, Arbitrary s, Arbitrary c) => Arbitrary (DFA s c) where
  arbitrary = do
    NonEmpty ss <- arbitrary
    NonEmpty cs <- arbitrary
    initial <- elements ss
    final   <- HS.fromList <$> sublistOf ss
    transition <- fmap M.fromList $ forM [(p, c) | p <- ss, c <- cs] $ \(p, c) ->
      ((p,c),) <$> elements ss
    return $ DFA { .. }

instance (Ord s, Ord c, Eq s, Hashable s, Arbitrary s, Arbitrary c) => Arbitrary (NFA s c) where
  arbitrary = do
    NonEmpty ss <- arbitrary
    NonEmpty cs <- arbitrary
    initialNFA <- elements ss
    finalNFA   <- HS.fromList <$> sublistOf ss
    transitionNFA <- fmap M.fromList $ listOf $ do
      s <- elements ss
      c <- elements cs
      qs <- HS.fromList <$> listOf1 (elements ss)
      return $ ((s, c), qs)
    return $ NFA { .. }

newtype RelevantDFA  = RelevantDFA { getDFA :: DFA Int [Bool] }
                       deriving (Show, Eq)

instance Arbitrary RelevantDFA where
  arbitrary = RelevantDFA . discardRedundant <$> arbitrary

prop_discardRedundant :: DFA Int Bool -> [Bool] -> Property
prop_discardRedundant d1 inp = accepts d1 inp === accepts (discardRedundant d1) inp

prop_intersection :: DFA Int Bool -> DFA Int Bool -> [Bool] -> Property
prop_intersection d1 d2 inp =
  let d' = d1 `intersection` d2
  in (accepts d1 inp && accepts d2 inp) === accepts d' inp

prop_union :: DFA Int Bool -> DFA Int Bool -> [Bool] -> Property
prop_union d1 d2 inp =
  let d' = d1 `union` d2
  in (accepts d1 inp || accepts d2 inp) === accepts d' inp

prop_minimize :: DFA Int Bool -> [Bool] -> Property
prop_minimize d inp = accepts d inp === accepts (minimize d) inp

-- To heavy...
-- prop_determinize :: NFA Int Bool -> [Bool] -> Property
-- prop_determinize d inp = acceptsNFA d inp === accepts (determinize d) inp
