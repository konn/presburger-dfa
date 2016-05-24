{-# LANGUAGE BangPatterns, DataKinds, DeriveDataTypeable, DeriveGeneric    #-}
{-# LANGUAGE FlexibleInstances, GADTs, LambdaCase, NamedFieldPuns          #-}
{-# LANGUAGE NoOverloadedLists, ParallelListComp, PatternGuards, PolyKinds #-}
{-# LANGUAGE RecordWildCards, ScopedTypeVariables, StandaloneDeriving      #-}
{-# LANGUAGE TupleSections, TypeFamilies, TypeOperators, ViewPatterns      #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Arithmetic.Presburger.Solver.DFA
       ( -- * Types
         Expr(..), Formula(..), Ident (Ident), Solution, Validity(..),
         liftFormula,
         -- * Solvers
         solve, isTautology, satisfiable, entail, getAllSolutions,
         -- * Internal functions and data-types
         buildDFA, buildDFAWith, getDFASolution,
         decodeSolution, DFA(..), encode, Bit(..)) where
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
import qualified Data.Sequence                    as S
import           Data.Vector                      (Vector)
import qualified Data.Vector                      as V
import           Unsafe.Coerce                    (unsafeCoerce)

-- | Solution (or Model) is a map assigning @'Integer'@s to each variable.
--   Variables without assingments are assumed to be @0@.
--
--   Since 0.1.0.0
type Solution = M.Map Ident Integer

-- | Validity of a given formula
--   Since 0.1.0.0
data Validity = Proved            -- ^ Given Formula is provable.
              | Refuted !Solution -- ^ Given Formula has coutnerexample(s).
              deriving (Show, Eq, Ord)

-- | @'entail' [f1, ..., fn] [g1, ..., gm]@ tries to prove
--   that @f1 :/\ ... :/\ fn@ implies @g1 :\/ ... :\/ gm@.
--
--   Since 0.1.0.0
entail :: [Formula n] -> [Formula m] -> Validity
entail prem goal = isTautology (foldr1 (:/\) prem :=> foldl1 (:\/) goal)

-- | Test if given formula is tautology.
--
--   Since 0.1.0.0
isTautology :: Formula m -> Validity
isTautology = maybe Proved Refuted . solve . Not

-- | @'solve phi'@ finds solutions for formula phi.
--   Note that @'solve'@ MAY NOT exhaust all possible solutions for the given formula.
solve :: Alternative f => Formula m -> f Solution
solve f =
  let (targ, vdic) = buildDFA $ encode f
  in asum $ map pure $ nub $ getDFASolution vdic targ
{-# INLINE solve #-}

-- | Check if the given formula is satisfiable
--
--   Since 0.1.0.0
satisfiable :: Formula m -> Bool
satisfiable = isJust . solve

-- | Find solutions consecutively applying @'solve'@.
--   N.B. This is SO slow.
--
--   Since 0.1.0.0
getAllSolutions :: Formula m -> [Solution]
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

toConstr :: Solution -> [Formula 'Raw]
toConstr dic = [ Not ((Var a :: Expr 'Raw) :== Num b) | (a, b) <- M.toList dic ]

class Encodable f where
  encode :: f m -> f 'Raw

instance Encodable Expr where
  encode (Var v) = Var v
  encode (n :- m) = encode $ n :+ (-1) :* m
  encode (Num i) = Num i
  encode (n :+ m) = encode n :+ encode m
  encode (n :* m) = n :* encode m

instance Encodable Formula where
  encode (Not  p)   = Not (encode p)
  encode (p :/\ q)  = encode p :/\ encode q
  encode (p :\/ q)  = encode p :\/ encode q
  encode (p :=> q)  = encode $ Not (encode p) :\/ encode q
  encode (Ex   v p) = Ex v (encode p)
  encode (Any  v p) = Not $ Ex v $ Not (encode p)
  encode (n :<= m)  = encode n :<= encode m
  encode (n :>= m)  = encode m :<= encode n
  encode (n :== m)  = encode n :== encode m
  encode (n :<  m)  =
    let (m', n') = (encode m, encode n)
    in encode $ n' :<= m' :/\ Not (n' :== m')
  encode (n :>  m)  = encode $ m :< n

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
  in (buildDFAWith varDic f, varDic)

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

buildDFAWith :: VarDic -> Formula 'Raw -> DFA Integer Bits
buildDFAWith vdic  (a :<= b) =
  let atomic = toAtomic vdic a b
  in renumberStates $ leqToDFA atomic
buildDFAWith vdic  (a :== b) =
  let atomic = toAtomic vdic a b
  in renumberStates $ eqToDFA atomic
buildDFAWith vdic (Not t) = complement $ buildDFAWith vdic t
buildDFAWith vdic (t1 :/\ t2) =
  let d1 = buildDFAWith vdic (encode t1)
      d2 = buildDFAWith vdic (encode t2)
  in renumberStates $ minimize $ d1 `intersection` d2
buildDFAWith vdic (t1 :\/ t2) =
  let d1 = buildDFAWith vdic (encode t1)
      d2 = buildDFAWith vdic (encode t2)
  in renumberStates $ minimize $ d1 `union` d2
buildDFAWith vdic (Ex v t)
  | v `notElem` vars t = buildDFAWith vdic t
  | otherwise =
    let idx = toInteger $ M.size vdic
        var = Anonymous $ 1 + maximum ((-1) : [i | Anonymous i <- M.keys vdic])
        dfa = buildDFAWith (M.insert var idx vdic) $ subst v var t
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
atomicToDFA chkFinal reduce Atomic{..} =
  let trans = loop (S.singleton upperBound) HS.empty M.empty
      dfa0  = DFA{ initial    = upperBound
                 , final      = HS.empty
                 , transition = trans
                 }
  in renumberStates $ minimize $ expandLetters inputs $ dfa0 { final = HS.filter chkFinal (states dfa0) }
  where
    inputs = V.replicateM (V.length coeffs) [O, I]
    loop (S.viewl -> k S.:< ws) qs trans =
      let qs' = HS.insert k qs
          targs  = map (\xi -> (xi, (k - (coeffs .*. xi)) `div` 2)) $
                   filter (reduce k) inputs
          trans' = M.fromList [ ((k, xi), j) | (xi, j) <- targs ]
          ws'  = S.fromList $ filter (not . (`HS.member` qs')) (map snd targs)
      in loop (ws S.>< ws') qs' (trans `M.union` trans')
    loop _ _ tr = tr

bitToInt :: Bit -> Integer
bitToInt O = 0
bitToInt I = 1
{-# INLINE bitToInt #-}

decodeSolution :: VarDic -> [Vector Bit] -> Solution
decodeSolution vdic vs
  | null vs = fmap (const 0) vdic
  | otherwise =
    let vvec = V.fromList $ map (foldr (\a b -> bitToInt a + 2*b) 0) $ transpose $ map V.toList vs
    in M.mapWithKey (const $ fromMaybe 0 . (vvec V.!?) . fromInteger) vdic

getDFASolution :: (Ord a, Hashable a, Alternative f) => VarDic -> DFA a (Vector Bit) -> f Solution
getDFASolution vdic dfa =
  let ss = walk dfa
  in asum $ map (pure . decodeSolution vdic . toList . snd) $ M.toList $
     M.filterWithKey (\k _ -> isFinal dfa k) ss
