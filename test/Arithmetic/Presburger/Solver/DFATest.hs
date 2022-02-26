{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Arithmetic.Presburger.Solver.DFATest where

import Arithmetic.Presburger.Solver.DFA
import Arithmetic.Presburger.Solver.Test.Shared ()
import qualified Data.Map as M
import Numeric.Natural (Natural)
import Test.QuickCheck.Instances ()
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

r, q, p, n, m, l :: Ident
[l, m, n, p, q, r] = map (Ident . pure) "lmnpqr"

test_falsity :: TestTree
test_falsity =
  testCase "Gives no solution for falsity" $
    solve (0 :== 1) @?= []

test_trivial :: TestTree
test_trivial =
  testCase "Solves 0 == 0" $
    solve (0 :== 0) @?= [M.empty]

natToInt :: Natural -> Integer
natToInt = toInteger

prop_solve_atomLeq :: Natural -> Integer -> Integer -> Property
prop_solve_atomLeq c d ub =
  let target = natToInt c :* Var n + d :* Var m
      anss = solve (target :<= Num ub) :: [Solution]
   in (null anss .&&. forAll arbitrary (\e f -> natToInt c * natToInt e + d * natToInt f > ub))
        .||. (not (null anss) .&&. conjoin [substitute sol target <= ub | sol <- anss])

test_regressions :: TestTree
test_regressions =
  testGroup
    "Regression tests"
    [ testCase "solves 2*n - m == 1" $ do
        let expr = 2 * Var n - Var m
            sols = solve (expr :== 1) :: [Solution]
        not (null sols) @? "Solution not found!"
        substitute (head sols) expr @?= 1
    ]

prop_solve_atomEq :: Natural -> Integer -> Integer -> Property
prop_solve_atomEq c d ub =
  let target = natToInt c :* Var n + d :* Var m
      anss = solve (target :== Num ub) :: [Solution]
   in counterexample "empty case" (null anss .&&. forAll arbitrary (\e f -> natToInt c * natToInt e + d * natToInt f =/= ub))
        .||. counterexample
          "invalid solution found"
          (not (null anss) .&&. conjoin [substitute sol target === ub | sol <- anss])
