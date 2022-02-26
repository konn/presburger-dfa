{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Arithmetic.Presburger.Solver.DFA as D
import Control.DeepSeq (NFData (..))
import Control.Exception (evaluate)
import Data.Hashable (hash)
import Data.List (nub, sort)
import GHC.Generics (Generic)
import Test.Tasty.Bench

linEqs :: [(String, Formula 'Extended)]
linEqs =
  [ ("degenerate bivariate", 2 :* Var n :- 3 :* Var m :== 5)
  ,
    ( "solvable two bivariate"
    , 2 :* Var n :- 3 :* Var m :== 5
        :/\ 3 :* Var n :+ 2 :* Var m :== 14
    )
  ,
    ( "unsolvable two bivariate"
    , 2 :* Var n :- 3 :* Var m :== 5
        :/\ 3 :* Var n :+ 2 :* Var m :== 13
    )
  ,
    ( "degenerate two trivariate"
    , 2 :* Var n :- 3 :* Var m :+ Var l :== 5
        :/\ 3 :* Var n :+ 2 :* Var m :== 13
    )
  ,
    ( "solvable three trivariate"
    , 2 :* Var n :- 3 :* Var m :+ Var l :== 5
        :/\ 3 :* Var n :+ 2 :* Var m :== 13
        :/\ Var n :+ Var m :+ Var l :== 24
    )
  ,
    ( "unsolvable three trivariate"
    , 2 :* Var n :- 3 :* Var m :+ Var l :== 5
        :/\ 3 :* Var n :+ 2 :* Var m :== 13
        :/\ Var n :+ Var m :+ Var l :== 25
    )
  ]
  where
    [l, m, n] = map (Ident . pure) "lmn"

linIneqs :: [(String, Formula 'Extended)]
linIneqs =
  [ ("trivial one bivariate", 2 :* Var n :- 3 :* Var m :<= 5)
  ,
    ( "two bivariate"
    , 2 :* Var n :- 3 :* Var m :<= 5
        :/\ 3 :* Var n :+ 2 :* Var m :> 14
    )
  ,
    ( "multiply of 7 in [10, 20)"
    , Var n :== 7 :* Var l :/\ 10 :<= Var n :/\ Var n :< 20
    )
  , ("falsity n < 0", Var n :< 0)
  ,
    ( "falsity 2n < n"
    , 2 :* Var n :< Var n
    )
  ,
    ( "solvable trivariate ineq+eq"
    , 2 :* Var n :- 3 :* Var m :+ Var l :== 5
        :/\ 3 :* Var n :+ 2 :* Var m :- Var l :== 3
        :/\ Var n :+ Var m :+ Var l :> 25
    )
  ,
    ( "unsolvable trivariate ineq+eq"
    , 2 :* Var n :- 3 :* Var m :+ Var l :== 5
        :/\ 3 :* Var n :+ 2 :* Var m :== 13
        :/\ Var n :+ Var m :+ Var l :> 25
    )
  ]
  where
    [l, m, n] = map (Ident . pure) "lmn"

mkSolveCase :: (String, Formula a) -> Benchmark
mkSolveCase (label, fml) =
  env (return $! fml) $ \d ->
    bgroup
      label
      [ bench "dfa" $ nf solveM d
      ]

solveM :: D.Formula a -> Maybe Solution
solveM = solve

main :: IO ()
main =
  defaultMain
    [ bgroup "Linear Equation" $ map mkSolveCase linEqs
    , bgroup "Linear Inequality" $ map mkSolveCase linIneqs
    ]
