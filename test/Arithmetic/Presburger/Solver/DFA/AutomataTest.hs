{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Arithmetic.Presburger.Solver.DFA.AutomataTest where

import Arithmetic.Presburger.Solver.DFA
import Arithmetic.Presburger.Solver.DFA.Automata
import Test.QuickCheck.Instances ()
import Test.QuickCheck.Property

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
