{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Arithmetic.Presburger.Solver.Test.Shared where

import Arithmetic.Presburger.Solver.DFA.Automata
import Control.Monad (forM)
import qualified Data.HashSet as HS
import Data.Hashable
import qualified Data.Map.Strict as M
import Test.Tasty.QuickCheck

instance (Ord s, Ord c, Eq s, Hashable s, Arbitrary s, Arbitrary c) => Arbitrary (DFA s c) where
  arbitrary = do
    NonEmpty ss <- arbitrary
    NonEmpty cs <- arbitrary
    initial <- elements ss
    final <- HS.fromList <$> sublistOf ss
    transition <- fmap M.fromList $
      forM [(p, c) | p <- ss, c <- cs] $ \(p, c) ->
        ((p, c),) <$> elements ss
    return DFA {..}

instance (Ord s, Ord c, Eq s, Hashable s, Arbitrary s, Arbitrary c) => Arbitrary (NFA s c) where
  arbitrary = do
    NonEmpty ss <- arbitrary
    NonEmpty cs <- arbitrary
    initialNFA <- elements ss
    finalNFA <- HS.fromList <$> sublistOf ss
    transitionNFA <- fmap M.fromList $
      listOf $ do
        s <- elements ss
        c <- elements cs
        qs <- HS.fromList <$> listOf1 (elements ss)
        return ((s, c), qs)
    return $ NFA {..}

newtype RelevantDFA = RelevantDFA {getDFA :: DFA Int [Bool]}
  deriving (Show, Eq)

instance Arbitrary RelevantDFA where
  arbitrary = RelevantDFA . discardRedundant <$> arbitrary
