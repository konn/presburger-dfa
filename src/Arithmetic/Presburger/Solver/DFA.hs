{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Arithmetic.Presburger.Solver.DFA
  ( -- * Types
    Expr' (..),
    Expr,
    Formula' (..),
    Formula,
    Ident (..),
    Solution,
    Validity (..),
    liftFormula,
    substitute,
    Mode (..),
    freeVars,

    -- * Solvers
    solve,
    isTautology,
    satisfiable,
    entail,
    leastSuch,
    minimized,

    -- * Internal functions and data-types
    buildDFA,
    buildDFAWith,
    getDFASolution,
    decodeSolution,
    DFA (..),
    encode,
    Bit (..),
  )
where

import Arithmetic.Presburger.Solver.DFA.Automata
import Arithmetic.Presburger.Solver.DFA.Types
import Control.Applicative (Alternative)
import Control.Arrow (first)
import Control.Monad.Trans.State.Strict (State, execState, get, gets, put)
import Data.Bit
import Data.DList (DList)
import qualified Data.DList as DL
import Data.Either (partitionEithers)
import Data.Foldable (asum, foldl', toList)
import qualified Data.HashSet as HS
import Data.Hashable (Hashable)
import Data.List (transpose)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as S
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Unsafe.Coerce (unsafeCoerce)

{- |
Solution (or Model) is a map assigning @'Integer'@s to each variable.
Variables without assingments are assumed to be @0@.

Since 0.1.0.0
-}
type Solution = M.Map Ident Integer

{- |
Validity of a given formula

Since 0.1.0.0
-}
data Validity
  = -- | Given Formula is provable.
    Proved
  | -- | Given Formula has coutnerexample(s).
    Refuted !Solution
  deriving (Show, Eq, Ord)

{- |
@'entail' [f1, ..., fn] [g1, ..., gm]@ tries to prove
that @f1 :/\ ... :/\ fn@ implies @g1 :\/ ... :\/ gm@.

Since 0.1.0.0
-}
entail :: [Formula n] -> [Formula m] -> Validity
entail prem goal = isTautology (foldr1 (:/\) prem :=> foldl1 (:\/) goal)

{- | Test if given formula is tautology.

Since 0.1.0.0
-}
isTautology :: Formula m -> Validity
isTautology = maybe Proved Refuted . solve . Not

{- |
@'solve phi'@ finds solutions for formula phi.
Note that @'solve'@ MAY NOT exhaust all possible solutions for the given formula.
-}
solve :: Alternative f => Formula m -> f Solution
solve f =
  let (targ, vdic) = buildDFA $ encode f
   in getDFASolution vdic targ
{-# INLINE solve #-}

{- |
Check if the given formula is satisfiable

Since 0.1.0.0
-}
satisfiable :: Formula m -> Bool
satisfiable = not . null . final . fst . buildDFA . encode

liftFormula :: Formula e -> Formula 'Extended
liftFormula = unsafeCoerce

class Encodable f where
  encode :: f m Ident -> f 'Raw Ident

instance Encodable Expr' where
  encode (Var v) = Var v
  encode (n :- m) = encode $ n :+ (-1) :* m
  encode (Num i) = Num i
  encode (n :+ m) = encode n :+ encode m
  encode (n :* m) = n :* encode m

instance Encodable Formula' where
  encode (Not p) = Not (encode p)
  encode (p :/\ q) = encode p :/\ encode q
  encode (p :\/ q) = encode p :\/ encode q
  encode (p :=> q) = encode $ Not (encode p) :\/ encode q
  encode (Ex v p) = Ex v (encode p)
  encode (Any v p) = Not $ Ex v $ Not (encode p)
  encode (n :<= m) = encode n :<= encode m
  encode (n :>= m) = encode m :<= encode n
  encode (n :== m) = encode n :== encode m
  encode (n :< m) =
    let (m', n') = (encode m, encode n)
     in encode $ n' :<= m' :/\ Not (n' :== m')
  encode (n :> m) = encode $ m :< n

-- | Minimizing operator
leastSuch :: Ident -> Formula m -> Formula 'Extended
leastSuch v f =
  let x = fresh f
   in f :/\ Any x (Var x :< Var v :=> Not (subst v x f))

minimized :: Formula m -> Formula 'Extended
minimized f = foldr ((.) . leastSuch) id (freeVars f) (liftFormula f)

type Summand = Either Integer (Ident, Integer)

summands :: Expr mode -> [Summand]
summands = DL.toList . loop
  where
    loop :: Expr mode -> DList Summand
    loop (n :* m :* t) = loop ((n * m) :* t)
    loop (n :- m) = loop (n :+ (-1) :* m)
    loop (0 :* _) = mempty
    loop (n :* Var i) = pure $ Right (i, n)
    loop (n :* Num m) = pure $ Left (n * m)
    loop (n :* (l :+ m)) = loop (n :* l) <> loop (n :* m)
    loop (n :* (l :- m)) = loop (n :* l) <> loop ((- n) :* m)
    loop (Var t) = pure $ Right (t, 1)
    loop (Num t) = pure $ Left t
    loop (t1 :+ t2) = loop t1 <> loop t2

type Index = Integer

type VarDic = M.Map Ident Integer

buildDFA :: Formula 'Raw -> (DFA Integer Bits, VarDic)
buildDFA f =
  let (_, varDic) = execState (mapM_ getIdx $ freeVars f) (0, M.empty)
   in (buildDFAWith varDic f, varDic)

toAtomic :: M.Map Ident Integer -> Expr mode1 -> Expr mode -> Atomic
toAtomic vdic a b =
  let (nb, pxs) = partitionEithers (summands a)
      (pb, nxs) = partitionEithers (summands b)
      cfs0 = M.unionWith (+) (M.fromList pxs) (negate <$> M.fromList nxs)
      ub = sum pb - sum nb
      len = M.size vdic
      cds = map (first (vdic M.!)) $ M.toList cfs0
      cfs = V.generate len $ \i -> fromMaybe 0 (lookup (toInteger i) cds)
   in Atomic cfs ub

buildDFAWith :: VarDic -> Formula 'Raw -> DFA Integer Bits
buildDFAWith vdic (a :<= b) =
  let atomic = toAtomic vdic a b
   in leqToDFA atomic
buildDFAWith vdic (a :== b) =
  let atomic = toAtomic vdic a b
   in eqToDFA atomic
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
  | v `notElem` freeVars t = buildDFAWith vdic t
  | otherwise =
    let idx = toInteger $ M.size vdic
        var = Anonymous $ 1 + maximum ((-1) : [i | Anonymous i <- M.keys vdic])
        dfa = buildDFAWith (M.insert var idx vdic) $ subst v var t
     in changeLetter (uncurry (U.++)) $
          minimize $
            renumberStates $
              determinize $
                projDFA $ changeLetter (splitNth idx) dfa

fresh :: Formula a -> Ident
fresh e = Anonymous $ 1 + maximum ((-1) : [i | Anonymous i <- Set.toList $ allVars e])

allVars :: Foldable f => f Ident -> Set Ident
allVars = foldl' (flip Set.insert) Set.empty

freeVars :: Formula a -> Set Ident
freeVars (ex :<= ex') = allVars ex <> allVars ex'
freeVars (ex :== ex') = allVars ex <> allVars ex'
freeVars (ex :< ex') = allVars ex <> allVars ex'
freeVars (ex :>= ex') = allVars ex <> allVars ex'
freeVars (ex :> ex') = allVars ex <> allVars ex'
freeVars (Not for') = freeVars for'
freeVars (for' :\/ for2) = freeVars for' <> freeVars for2
freeVars (for' :/\ for2) = freeVars for' <> freeVars for2
freeVars (for' :=> for2) = freeVars for' <> freeVars for2
freeVars (Ex bound for') = Set.delete bound $ freeVars for'
freeVars (Any bound for') = Set.delete bound $ freeVars for'

splitNth :: U.Unbox a => Integer -> U.Vector a -> ((U.Vector a, U.Vector a), a)
splitNth n v =
  let (hd, tl) = U.splitAt (fromInteger n) v
   in ((hd, U.tail tl), U.head tl)

type BuildingEnv = (Index, M.Map Ident Index)

getIdx :: Ident -> State BuildingEnv Index
getIdx ident =
  gets (M.lookup ident . snd) >>= \case
    Just i -> return i
    Nothing -> do
      (i, dic) <- get
      put (i + 1, M.insert ident i dic)
      return i

data Atomic = Atomic
  { coeffs :: V.Vector Integer
  , upperBound :: Integer
  }
  deriving (Read, Show, Eq, Ord)

type MachineState = Integer

eqToDFA :: Atomic -> DFA MachineState Bits
eqToDFA a@Atomic {..} = atomicToDFA (== 0) (\k xi -> even (k - coeffs .*. xi)) a

leqToDFA :: Atomic -> DFA MachineState Bits
leqToDFA = atomicToDFA (>= 0) (const $ const True)

atomicToDFA ::
  -- | Is final state?
  (Integer -> Bool) ->
  -- | Candidate reducer
  (Integer -> Bits -> Bool) ->
  Atomic ->
  DFA Integer (Bits)
atomicToDFA chkFinal reduce Atomic {..} =
  let trans = loop (S.singleton upperBound) HS.empty M.empty
      dfa0 =
        DFA
          { initial = upperBound
          , final = HS.empty
          , transition = trans
          }
   in renumberStates $ minimize $ expandLetters inputs $ dfa0 {final = HS.filter chkFinal (states dfa0)}
  where
    inputs = U.replicateM (V.length coeffs) [O, I]
    loop (S.viewl -> k S.:< ws) qs trans =
      let qs' = HS.insert k qs
          targs =
            map (\xi -> (xi, (k - (coeffs .*. xi)) `div` 2)) $
              filter (reduce k) inputs
          trans' = M.fromList [((k, xi), j) | (xi, j) <- targs]
          ws' = S.fromList $ filter (not . (`HS.member` qs')) (map snd targs)
       in loop (ws S.>< ws') qs' (trans `M.union` trans')
    loop _ _ tr = tr

bitToInt :: Bit -> Integer
bitToInt O = 0
bitToInt I = 1
{-# INLINE bitToInt #-}

substitute :: Solution -> Expr a -> Integer
substitute dic (Var e) = fromMaybe 0 $ M.lookup e dic
substitute _ (Num e) = e
substitute dic (e1 :+ e2) = substitute dic e1 + substitute dic e2
substitute dic (e1 :- e2) = substitute dic e1 - substitute dic e2
substitute dic (e1 :* e2) = e1 * substitute dic e2

decodeSolution :: VarDic -> [Bits] -> Solution
decodeSolution vdic vs
  | null vs = fmap (const 0) vdic
  | otherwise =
    let vvec = V.fromList $ map (foldr (\a b -> bitToInt a + 2 * b) 0) $ transpose $ map U.toList vs
     in M.mapWithKey (const $ fromMaybe 0 . (vvec V.!?) . fromInteger) vdic

getDFASolution :: (Ord a, Hashable a, Alternative f) => VarDic -> DFA a (Bits) -> f Solution
getDFASolution vdic dfa =
  let ss = walk dfa
   in asum $
        map (pure . decodeSolution vdic . toList . snd) $
          M.toList $
            M.filterWithKey (\k _ -> isFinal dfa k) ss
