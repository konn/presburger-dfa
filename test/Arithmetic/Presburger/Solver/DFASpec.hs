{-# LANGUAGE DataKinds, RecordWildCards, ScopedTypeVariables, TupleSections #-}
{-# LANGUAGE ViewPatterns                                                   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Arithmetic.Presburger.Solver.DFASpec where
import Arithmetic.Presburger.Solver.DFA

import           Control.Monad             (forM)
import           Data.Hashable             (Hashable)
import qualified Data.HashSet              as HS
import qualified Data.Map                  as M
import           GHC.Exts                  (fromList)
import           Numeric.Natural           (Natural)
import           Test.QuickCheck.Instances ()
import           Test.Tasty.Discover

r, q, p, n, m, l :: Ident
[l, m, n, p, q, r] = map (Ident . pure) "lmnpqr"

case_falsity :: Assertion
case_falsity = solve (0 :== 1) @?= [  ]

case_trivial :: Assertion
case_trivial = solve (0 :== 0) @?= [M.fromList []]

natToInt :: Natural -> Integer
natToInt = toInteger

prop_solve_atomLeq :: Integer -> Integer -> Integer -> Property
prop_solve_atomLeq c d ub =
  let target = abs c :* Var n + d :* Var m
      anss = solve (target  :<= Num ub) :: [Solution]
  in  (null anss .&&. forAll arbitrary (\e f -> abs c * natToInt e + d * natToInt f > ub))
  .||. (not (null anss) .&&. conjoin [ substitute sol target <= ub | sol <- anss])

prop_solve_atomEq :: Integer -> Integer -> Integer -> Property
prop_solve_atomEq c d ub =
  let target = abs c :* Var n + d :* Var m
      anss = solve (target  :== Num ub) :: [Solution]
  in  (null anss .&&. forAll arbitrary (\e f -> abs c * natToInt e + d * natToInt f /= ub))
  .||. (not (null anss) .&&. conjoin [ substitute sol target === ub | sol <- anss])
