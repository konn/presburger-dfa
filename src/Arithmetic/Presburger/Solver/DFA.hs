{-# LANGUAGE BangPatterns, DataKinds, DeriveDataTypeable, DeriveGeneric    #-}
{-# LANGUAGE FlexibleInstances, GADTs, LambdaCase, NamedFieldPuns          #-}
{-# LANGUAGE NoOverloadedLists, ParallelListComp, PatternGuards, PolyKinds #-}
{-# LANGUAGE RecordWildCards, ScopedTypeVariables, StandaloneDeriving      #-}
{-# LANGUAGE TupleSections, TypeFamilies, TypeOperators, ViewPatterns      #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Arithmetic.Presburger.Solver.DFA
       ( -- * Types
         Expr(..), Formula(..), Ident (Ident), Valuation,
         liftFormula,
         -- * Solvers
         solve, isTautology, satisfiable, entail, getAllSolutions,
         -- * Internal functions and data-types
         buildDFA, decodeSolution, DFA(..), encode) where
import Arithmetic.Presburger.Solver.DFA.Automata
import Arithmetic.Presburger.Solver.DFA.Types

import           Control.Applicative              (Alternative)
import           Control.Arrow                    (first)
import           Control.Monad.Trans.State.Strict (State, execState, get, gets)
import           Control.Monad.Trans.State.Strict (put)
import           Data.Either                      (partitionEithers)
import           Data.Foldable                    (asum, toList)
import           Data.Hashable                    (Hashable)
import qualified Data.HashSet                     as HS
import           Data.List                        (nub, sort, transpose)
import qualified Data.Map.Strict                  as M
import           Data.Maybe                       (fromMaybe, isJust)
import           Data.Vector                      (Vector)
import qualified Data.Vector                      as V
import           Unsafe.Coerce                    (unsafeCoerce)

type Valuation = M.Map Ident Integer


-- | @'entail' [f1, ..., fn] [g1, ..., gm]@ proves @f1 :/\ ... :/\ fn :==> g1 :\/ ... :\/ gm@.
entail :: [Formula n] -> [Formula m] -> Bool
entail prem goal = isTautology (foldr1 (:/\) prem :=> foldl1 (:\/) goal)

-- | Test if given formula is tautology.
isTautology :: Formula m -> Bool
isTautology = null . flip asTypeOf [] . solve . Not

-- | @'solve phi'@ finds solutions for formula phi.
solve :: Alternative f => Formula m -> f Valuation
solve f =
  let (targ, vdic) = buildDFA $ encode f
      len = M.size vdic
  in asum $ map pure $ nub $ map (\sol -> fmap ((sol !!) . fromInteger) vdic) $ getSolution len targ
{-# INLINE solve #-}

satisfiable :: Formula m -> Bool
satisfiable = isJust . solve

-- | Find solutions consecutively applying @'solve'@.
--   N.B. This is SO slow.
getAllSolutions :: Formula m -> [Valuation]
getAllSolutions = loop
  where
    loop f =
      let sols = solve (minimized f)
      in if null sols
         then []
         else sols ++ loop (foldr (:/\) f $ concatMap toConstr sols)
{-# INLINE getAllSolutions #-}

liftFormula :: Formula e -> Formula 'Extended
liftFormula = unsafeCoerce

toConstr :: Valuation -> [Formula 'Raw]
toConstr dic = [ Not ((Var a :: Expr 'Raw) :== Num b) | (a, b) <- M.toList dic ]

-- | Minimizing operator
leastSuch :: Ident -> Formula m -> Formula 'Extended
leastSuch v f =
  let x = fresh f
  in f :/\ Any x (Var x :< Var v :=> Not (subst v x f))

minimized :: Formula m -> Formula 'Extended
minimized f = foldr ((.) . leastSuch) id (vars f) (liftFormula f)

type Summand = Either Integer (Ident, Integer)

summands :: Expr mode -> [Summand]
summands (n :* m :* t) = summands ((n * m) :* t)
summands (n :- m)     = summands (n :+ (-1) :* m)
summands (0 :* _)     = []
summands (n :* Var i) = [Right (i, n)]
summands (n :* Num m) = [Left (n * m)]
summands (n :* (l :+ m)) = summands (n :* l) ++ summands (n :* m)
summands (n :* (l :- m)) = summands (n :* l) ++ summands ((-n) :* m)
summands (Var t) = [Right (t, 1)]
summands (Num t) = [Left t]
summands (t1 :+ t2) = summands t1 ++ summands t2

type Index = Integer
type VarDic = M.Map Ident Integer

buildDFA :: Formula 'Raw -> (DFA Integer Bits, VarDic)
buildDFA f =
  let (_, varDic) = execState (mapM getIdx $ sort (vars f)) (0, M.empty)
  in (buildDFA' varDic f, varDic)

toAtomic :: M.Map Ident Integer -> Expr mode1 -> Expr mode -> Atomic
toAtomic vdic a b =
  let (nb, pxs) = partitionEithers (summands a)
      (pb, nxs) = partitionEithers (summands b)
      cfs0 = M.unionWith (+) (M.fromList pxs) (fmap negate $ M.fromList nxs)
      ub = sum pb - sum nb
      len = M.size vdic
      cds = map (first (vdic M.!)) $ M.toList cfs0
      cfs = V.generate len $ \i -> fromMaybe 0 (lookup (toInteger i) cds)
  in Atomic cfs ub

buildDFA' :: VarDic -> Formula 'Raw -> DFA Integer Bits
buildDFA' vdic  (a :<= b) =
  let atomic = toAtomic vdic a b
  in renumberStates $ leqToDFA atomic
buildDFA' vdic  (a :== b) =
  let atomic = toAtomic vdic a b
  in renumberStates $ eqToDFA atomic
buildDFA' vdic (Not t) = complement $ buildDFA' vdic t
buildDFA' vdic (t1 :/\ t2) =
  let d1 = buildDFA' vdic (encode t1)
      d2 = buildDFA' vdic (encode t2)
  in renumberStates $ minimize $ d1 `intersection` d2
buildDFA' vdic (t1 :\/ t2) =
  let d1 = buildDFA' vdic (encode t1)
      d2 = buildDFA' vdic (encode t2)
  in renumberStates $ minimize $ d1 `join` d2
buildDFA' vdic (Ex v t)
  | v `notElem` vars t = buildDFA' vdic t
  | otherwise =
    let idx = toInteger $ M.size vdic
        var = Anonymous $ 1 + maximum ((-1) : [i | Anonymous i <- M.keys vdic])
        dfa = buildDFA' (M.insert var idx vdic) $ subst v var t
    in changeLetter (uncurry (V.++)) $
       minimize $ renumberStates $ determinize $
       projDFA $ changeLetter (splitNth idx) dfa

fresh :: Formula a -> Ident
fresh e = Anonymous $ 1 + maximum ((-1) : [i | Anonymous i <- allVarsF e])

allVarsF :: Formula a -> [Ident]
allVarsF (e1 :<= e2) = nub $ vars e1 ++ vars e2
allVarsF (e1 :== e2) = nub $ vars e1 ++ vars e2
allVarsF (e1 :< e2) = nub $ vars e1 ++ vars e2
allVarsF (e1 :>= e2) =  nub $ vars e1 ++ vars e2
allVarsF (e1 :> e2) = nub $ vars e1 ++ vars e2
allVarsF (Not e) = allVarsF e
allVarsF (e1 :\/ e2) = nub $ allVarsF e1 ++ allVarsF e2
allVarsF (e1 :/\ e2) = nub $ allVarsF e1 ++ allVarsF e2
allVarsF (e1 :=> e2) = nub $ allVarsF e1 ++ allVarsF e2
allVarsF (Ex e1 e2) = nub $ e1 : allVarsF e2
allVarsF (Any e1 e2) = nub $ e1 : allVarsF e2

splitNth :: Integer -> Vector a -> ((Vector a, Vector a), a)
splitNth n v =
  let (hd, tl) = V.splitAt (fromInteger n) v
  in ((hd, V.tail tl), V.head tl)

type BuildingEnv = (Index, M.Map Ident Index)

getIdx :: Ident -> State BuildingEnv Index
getIdx ident = gets (M.lookup ident . snd) >>= \case
  Just i -> return i
  Nothing -> do
    (i, dic) <- get
    put (i+1, M.insert ident i dic)
    return i


data Atomic = Atomic { coeffs     :: Vector Integer
                     , upperBound :: Integer
                     }
                deriving (Read, Show, Eq, Ord)

type MachineState  = Integer

eqToDFA ::  Atomic -> DFA MachineState Bits
eqToDFA a@Atomic{..} = atomicToDFA (== 0) (\k xi -> even (k - coeffs .*. xi)) a

leqToDFA :: Atomic -> DFA MachineState Bits
leqToDFA = atomicToDFA (>= 0) (const $ const True)

atomicToDFA :: (Integer -> Bool)               -- ^ Is final state?
            -> (Integer -> Vector Bit -> Bool) -- ^ Candidate reducer
            -> Atomic -> DFA Integer (Vector Bit)
atomicToDFA chkFinal reduce Atomic{..} = minimize $ loop [upperBound] HS.empty
                   DFA{ initial = upperBound
                      , transition = M.empty
                      , final = HS.empty
                      }
  where
    inputs = V.replicateM (V.length coeffs) [O, I]
    loop [] _ dfa = dfa
    loop (q : qs) seen d@DFA{final = fs} =
      let fs' | chkFinal q = HS.insert q fs
              | otherwise  = fs
          (dfa', seen', qs') =
            foldr step (d { final = fs' }, seen, qs) $
            filter (reduce q) inputs
      in loop qs' seen'  dfa'
      where
        step i (DFA{..}, sn, ps) =
          let j = (q - (coeffs .*. i))`div` 2
              ps' | HS.member j sn = ps
                  | otherwise = j : ps
          in (DFA{ transition = M.insert (q, i) j transition
                 , ..}, HS.insert j sn, ps')

bitToInt :: Bit -> Integer
bitToInt O = 0
bitToInt I = 1
{-# INLINE bitToInt #-}

decodeSolution :: Int -> [Vector Bit] -> [Integer]
decodeSolution len vs
  | null vs = replicate len 0
  | otherwise = map (foldr (\a b -> bitToInt a + 2*b) 0) $ transpose $ map V.toList vs

getSolution :: (Ord a, Hashable a) => Int -> DFA a (Vector Bit) -> [[Integer]]
getSolution l dfa =
  let ss = walk dfa
  in map (decodeSolution l . toList . snd) $ M.toList $
     M.filterWithKey (\k _ -> isFinal dfa k) ss
