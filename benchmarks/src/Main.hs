{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Arithmetic.Presburger.Solver.DFA as D
import Control.DeepSeq (NFData (..))
import Control.Exception (evaluate)
import qualified Data.DList as DL
import Data.Hashable (hash)
import qualified Data.Integer.SAT as P
import Data.List (nub, sort)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Test.Tasty.Bench

toPE :: D.Expr a -> P.Expr
toPE (D.Var t) = P.Var (identToName t)
toPE (D.Num t) = P.K t
toPE (t1 D.:+ t2) = toPE t1 P.:+ toPE t2
toPE (t1 D.:- t2) = toPE t1 P.:- toPE t2
toPE (t1 D.:* t2) = t1 P.:* toPE t2

varsPE :: P.Expr -> Set P.Name
varsPE (t1 P.:+ t2) = varsPE t1 <> varsPE t2
varsPE (t1 P.:- t2) = varsPE t1 <> varsPE t2
varsPE (_ P.:* t2) = varsPE t2
varsPE (P.Negate t) = varsPE t
varsPE (P.Var t) = Set.singleton t
varsPE (P.K _) = mempty
varsPE (P.If t1 t2 t3) = varsPP t1 <> varsPE t2 <> varsPE t3
varsPE (P.Div t1 _) = varsPE t1
varsPE (P.Mod t1 _) = varsPE t1
varsPE (P.Min l r) = varsPE l <> varsPE r
varsPE (P.Max l r) = varsPE l <> varsPE r

varsPP :: P.Prop -> Set P.Name
varsPP P.PTrue = mempty
varsPP P.PFalse = mempty
varsPP (p1 P.:|| p2) = varsPP p1 <> varsPP p2
varsPP (p1 P.:&& p2) = varsPP p1 <> varsPP p2
varsPP (P.Not p) = varsPP p
varsPP (p1 P.:== p2) = varsPE p1 <> varsPE p2
varsPP (p1 P.:/= p2) = varsPE p1 <> varsPE p2
varsPP (p1 P.:< p2) = varsPE p1 <> varsPE p2
varsPP (p1 P.:> p2) = varsPE p1 <> varsPE p2
varsPP (p1 P.:<= p2) = varsPE p1 <> varsPE p2
varsPP (p1 P.:>= p2) = varsPE p1 <> varsPE p2

toPF :: D.Formula a -> P.Prop
toPF f = nonNegP $ toPF' f

nonNegP :: P.Prop -> P.Prop
nonNegP p = foldr (P.:&&) p [P.Var n P.:>= P.K 0 | n <- Set.toList $ varsPP p]

toPF' :: D.Formula a -> P.Prop
toPF' (f1 D.:<= f2) = toPE f1 P.:<= toPE f2
toPF' (f1 D.:== f2) = toPE f1 P.:== toPE f2
toPF' (f1 D.:< f2) = toPE f1 P.:< toPE f2
toPF' (f1 D.:>= f2) = toPE f1 P.:>= toPE f2
toPF' (f1 D.:> f2) = toPE f1 P.:> toPE f2
toPF' (D.Not f) = P.Not (toPF f)
toPF' (f1 D.:\/ f2) = toPF' f1 P.:|| toPF' f2
toPF' (f1 D.:/\ f2) = toPF' f1 P.:&& toPF' f2
toPF' (f1 D.:=> f2) = P.Not (toPF' f1) P.:|| toPF' f2
toPF' (D.Ex _ _) = error "Only QF-form is supported"
toPF' (D.Any _ _) = error "Only QF-form is supported"

identToName :: D.Ident -> P.Name
identToName (D.Anonymous n) = P.toName $ 2 * n
identToName (D.Ident s) = P.toName $ 2 * hash s + 1

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
  env (pure (fml, toPF fml)) $ \ ~(d, p) ->
    bgroup
      label
      [ bench "dfa" $ nf solveM d
      , bench "pre" $ nf P.checkSat $ p `P.assert` P.noProps
      ]

solveM :: D.Formula a -> Maybe Solution
solveM = solve

main :: IO ()
main =
  defaultMain
    [ bgroup "Linear Equation" $ map mkSolveCase linEqs
    , bgroup "Linear Inequality" $ map mkSolveCase linIneqs
    ]
