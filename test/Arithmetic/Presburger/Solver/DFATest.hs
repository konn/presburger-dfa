{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Arithmetic.Presburger.Solver.DFATest where

import Arithmetic.Presburger.Solver.DFA
import Arithmetic.Presburger.Solver.Test.Shared ()
import Control.Monad (forM_)
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

solves :: Expr 'Extended -> Expr 'Extended -> TestTree
solves lhs rhs = testCase ("solves " <> show (lhs :== rhs :: Formula 'Extended)) $ do
  let sols = solve (lhs :== rhs) :: [Solution]
  not (null sols) @? "Solution not found!"
  forM_ sols $ \sol ->
    substitute sol lhs @?= substitute sol rhs

solvesLeq :: Expr s -> Expr s -> TestTree
solvesLeq lhs rhs = testCase ("solves " <> show ineq) $ do
  let sols = solve ineq :: [Solution]
  not (null sols) @? "Solution not found!"
  forM_ sols $ \sol -> do
    let subs = substitute sol
        lhs' = subs lhs
        rhs' = subs rhs
    lhs' <= rhs' @? "Invalid solution: " <> show lhs' <> " > " <> show rhs'
  where
    ineq :: Formula _
    ineq = lhs :<= rhs

solvesLeqs :: [(Expr 'Extended, Expr 'Extended)] -> TestTree
solvesLeqs lrhs = testCase ("solves " <> show ineq) $ do
  let sols = solve ineq :: [Solution]
  not (null sols) @? "Solution not found!"
  forM_ sols $ \sol ->
    forM_ lrhs $ \(lhs, rhs) -> do
      let subs = substitute sol
      let lhs' = subs lhs
          rhs' = subs rhs
      lhs' <= rhs' @? "Invalid solution: " <> show lhs' <> " > " <> show rhs'
  where
    ineq :: Formula _
    ineq = foldr1 (:/\) $ map (uncurry (:<=)) lrhs

refutes :: Formula s -> TestTree
refutes fml = testCase ("refutes " <> show fml) $ do
  let sols = solve fml :: [Solution]
  null sols @? "Invalid solution(s) found: " <> show sols

test_regressions :: TestTree
test_regressions =
  testGroup
    "Regression tests"
    [ solves (2 * Var n - Var m) 1
    , solvesLeq (2 :* Var n :- 3 :* Var m) 5
    , solvesLeqs
        [ (2 :* Var n :- 3 :* Var n, 5)
        , (3 :* Var n :+ (2 :* Var m :: Expr 'Extended), 14)
        ]
    , testCase "Solves multiply of 7 in [10, 20)" $ do
        let fml = Var n :== 7 :* Var l :/\ 10 :<= Var n :/\ Var n :< 20
            sols = solve fml :: [Solution]
        not (null sols) @? "No solution found!"
        forM_ sols $ \sol -> do
          let n' = substitute sol (Var n)
              l' = substitute sol (Var l)
          7 * l' @?= n'
          10 <= n' @? "n < 10"
          n' < 20 @? "n >= 20"
    , let leqL, leqR, gtL, gtR :: Expr 'Extended
          (leqL, leqR) = (2 :* Var n :- 3 :* Var m, 5)
          (gtL, gtR) = (3 :* Var n :+ (2 :* Var m :: Expr 'Extended), 14)
          fml :: Formula 'Extended
          fml = (leqL :<= leqR) :/\ (gtL :> gtR)
       in testCase ("solves " <> show fml) $ do
            let sols = solve fml :: [Solution]
            not (null sols) @? "No solution found!"
            forM_ sols $ \sol -> do
              let sub = substitute sol
              sub leqL <= sub leqR @? show (sub leqL) <> " > " <> show (sub leqR)
              sub gtL > sub gtR @? show (sub gtL) <> " <= " <> show (sub gtR)
    , let eq1L, eq1R, eq2L, eq2R, gtL, gtR :: Expr 'Extended
          (eq1L, eq1R) = (2 :* Var n :- 3 :* Var m :+ Var l, 5)
          (eq2L, eq2R) = (3 :* Var n :+ 2 :* Var m :- Var l, 3)
          (gtL, gtR) = (Var n :+ Var m :+ (Var l :: Expr 'Extended), 25)
          fml :: Formula 'Extended
          fml = (eq1L :== eq1R) :/\ (eq2L :== eq2R) :/\ (gtL :> gtR)
       in testCase ("solves " <> show fml) $ do
            let sols = solve fml :: [Solution]
            not (null sols) @? "No solution found!"
            forM_ sols $ \sol -> do
              let sub = substitute sol
              sub eq1L @?= sub eq1R
              sub eq2L @?= sub eq2R
              sub gtL > sub gtR @? show (sub gtL) <> " <= " <> show (sub gtR)
    , refutes $ Var n :< 0
    , refutes $ 2 :* Var n :< Var n
    , refutes $
        2 :* Var n :- 3 :* Var m :+ Var l :== 5
          :/\ 3 :* Var n :+ 2 :* Var m :== 13
          :/\ Var n :+ Var m :+ Var l :> 25
    ]

prop_solve_atomEq :: Natural -> Integer -> Integer -> Property
prop_solve_atomEq c d ub =
  let target = natToInt c :* Var n + d :* Var m
      anss = solve (target :== Num ub) :: [Solution]
   in counterexample "empty case" (null anss .&&. forAll arbitrary (\e f -> natToInt c * natToInt e + d * natToInt f =/= ub))
        .||. counterexample
          "invalid solution found"
          (not (null anss) .&&. conjoin [substitute sol target === ub | sol <- anss])
