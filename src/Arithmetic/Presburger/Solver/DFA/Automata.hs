{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields -fno-warn-type-defaults #-}

module Arithmetic.Presburger.Solver.DFA.Automata where

import Control.Arrow (first, second)
import Control.Monad (filterM, forM_, unless)
import Control.Monad.Trans.State.Strict (execState, gets, modify)
import qualified Data.Bifunctor as Bi
import Data.Foldable (any, minimumBy, toList)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Hashable (Hashable)
import Data.List (nub, partition)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe (fromJust, fromMaybe, mapMaybe, maybeToList)
import Data.Monoid (First (..), getFirst)
import Data.Ord (comparing)
import Data.Sequence (Seq)
import qualified Data.Sequence as S
import qualified Data.Set as Set
import Data.Traversable (for)
import GHC.Exts (fromList)
import GHC.Generics (Generic)
import Prelude hiding (any)

states :: (Eq s, Hashable s) => DFA s c -> HashSet s
states DFA {..} = fromList $ initial : concat [[t, s] | ((t, _), s) <- M.toList transition]

data DFA s c = DFA
  { initial :: s
  , final :: HashSet s
  , transition :: Map (s, c) s
  }
  deriving (Show, Eq)

isFinal :: (Eq a, Hashable a) => DFA a c -> a -> Bool
isFinal DFA {..} q = q `HS.member` final

boolOp ::
  (Eq c, Ord c, Hashable s, Hashable t, Ord s, Ord t) =>
  (Bool -> Bool -> Bool) ->
  DFA s c ->
  DFA t c ->
  DFA (Trapped s, Trapped t) c
boolOp = boolOpWith (,)

boolOpWith ::
  ( Eq s
  , Eq t
  , Ord s
  , Hashable s
  , Hashable t
  , Ord t
  , Eq u
  , Ord u
  , Hashable u
  , Eq c
  , Ord c
  ) =>
  (Trapped s -> Trapped t -> u) ->
  (Bool -> Bool -> Bool) ->
  DFA s c ->
  DFA t c ->
  DFA u c
boolOpWith tpl op d1'0 d2'0 =
  let inputs = nub $ letters d1'0 ++ letters d2'0
      (d1, d2) = (expandLetters inputs d1'0, expandLetters inputs d2'0)
      ss =
        [ (s, t)
        | s <- HS.toList (states d1)
        , t <- HS.toList (states d2)
        ]

      trans =
        fromList
          [ ((tpl s t, l), tpl s' t')
          | l <- inputs
          , (s, t) <- ss
          , s' <- maybeToList (feed d1 s l)
          , t' <- maybeToList (feed d2 t l)
          ]

      fs =
        fromList
          [ tpl s t | (s, t) <- ss, isFinal d1 s `op` isFinal d2 t
          ]
   in DFA
        { initial = tpl (initial d1) (initial d2)
        , transition = trans
        , final = fs
        }

intersection :: (Eq c, Ord c, Hashable s, Hashable t, Ord s, Ord t) => DFA s c -> DFA t c -> DFA (Trapped s, Trapped t) c
intersection = boolOp (&&)

intersectionWith ::
  (Eq c, Ord c, Hashable s, Hashable t, Hashable u, Ord s, Ord t, Ord u) =>
  (Trapped s -> Trapped t -> u) ->
  DFA s c ->
  DFA t c ->
  DFA u c
intersectionWith f = boolOpWith f (&&)

union :: (Eq c, Ord c, Hashable s, Hashable t, Ord s, Ord t) => DFA s c -> DFA t c -> DFA (Trapped s, Trapped t) c
union = boolOp (||)

unionWith ::
  (Eq c, Ord c, Hashable s, Hashable t, Hashable u, Ord s, Ord t, Ord u) =>
  (Trapped s -> Trapped t -> u) ->
  DFA s c ->
  DFA t c ->
  DFA u c
unionWith f = boolOpWith f (||)

data NFA s c = NFA
  { initialNFA :: s
  , finalNFA :: HashSet s
  , transitionNFA :: Map (s, c) (HashSet s)
  }
  deriving (Show, Eq)

projDFA :: (Ord a, Ord s, Hashable s) => DFA s (a, b) -> NFA s a
projDFA DFA {..} =
  let finalNFA = final
      initialNFA = initial
      transitionNFA =
        M.mapKeysWith HS.union (Bi.second fst) $
          fmap HS.singleton transition
   in NFA {..}

renumberStates :: (Enum s, Eq a, Num s, Ord s, Ord c, Hashable a, Hashable s) => DFA a c -> DFA s c
renumberStates dfa@DFA {initial = ini, final = fs, transition = trans} =
  let ss = states dfa
      idxDic = fromList $ zip (HS.toList $ HS.insert ini ss) [0 ..]
      initial = idxDic HM.! ini
      final = HS.map (idxDic HM.!) $ fs `HS.intersection` HS.insert ini ss
      transition = M.mapKeys (first (idxDic HM.!)) $ fmap (idxDic HM.!) trans
   in DFA {..}

statesNFA :: (Eq a, Hashable a) => NFA a t -> HashSet a
statesNFA NFA {..} = fromList $ initialNFA : concat [t : HS.toList s | ((t, _), s) <- M.toList transitionNFA]

-- | Naive Subset construction
determinize :: (Ord c, Eq s, Hashable s, Ord s) => NFA s c -> DFA [s] c
determinize = determinizeWith id

determinizeWith ::
  (Ord c, Eq s, Hashable s, Ord s, Eq s', Hashable s', Ord s') =>
  ([s] -> s') ->
  NFA s c ->
  DFA s' c
determinizeWith f n@NFA {..} =
  let sts = map (Set.toList . Set.fromList) $ filterM (const [True, False]) $ HS.toList $ statesNFA n
      final = HS.fromList $ map f $ filter (any (`HS.member` finalNFA)) sts
      initial = f [initialNFA]
      inputs = nub $ map snd $ M.keys transitionNFA
      transition =
        fromList
          [ ( (f ss, l)
            , f $
                concat $
                  mapMaybe
                    (\s -> HS.toList <$> M.lookup (s, l) transitionNFA)
                    ss
            )
          | ss <- sts
          , l <- inputs
          ]
   in DFA {..}

nubbing :: (Eq a, Hashable a) => [a] -> [a]
nubbing = toList . HS.fromList

getElem :: Foldable t => t a -> a
getElem = fromJust . getFirst . foldMap (First . Just)

quotient :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> [HashSet s] -> DFA s c
quotient DFA {initial = ini, final = fs, transition = tr} (filter (not . HS.null) -> reps) =
  let dic = fromList [(s, getElem r) | r <- reps, s <- HS.toList r]
      look v = fromMaybe v $ HM.lookup v dic
      initial = look ini
      final = HS.map look fs
      transition = M.mapKeys (first look) $ fmap look tr
   in DFA {..}

data Trapped a = Normal !a | Trap
  deriving (Eq, Ord, Generic, Hashable, Functor, Foldable, Traversable)

instance Applicative Trapped where
  pure = Normal
  Trap <*> _ = Trap
  _ <*> Trap = Trap
  Normal f <*> Normal a = Normal (f a)
  {-# INLINE (<*>) #-}

instance Monad Trapped where
  Trap >>= _ = Trap
  Normal a >>= f = f a
  {-# INLINE (>>=) #-}

instance (Show a) => Show (Trapped a) where
  show Trap = "⊥"
  show (Normal a) = show a

expandLetters :: (Ord a, Ord c, Hashable a) => [c] -> DFA a c -> DFA (Trapped a) c
expandLetters = expandLettersWith id

-- Do we need this at all?
expandLettersWith ::
  (Ord b, Ord c, Hashable a1, Eq a1, Hashable b) =>
  (Trapped a1 -> b) ->
  [c] ->
  DFA a1 c ->
  DFA b c
expandLettersWith unTrap cs d0 =
  let DFA {transition = trans, ..} = changeState mapQ d0
      ls = fromList cs `Set.union` fromList (letters d0)
      trap = unTrap Trap
      mapQ = unTrap . Normal
      transition =
        trans
          `M.union` fromList
            [ ((mapQ q, c), trap)
            | c <- Set.toList ls
            , q <- HS.toList $ states d0
            , not ((mapQ q, c) `Set.member` M.keysSet trans)
            ]
          `M.union` fromList [((trap, c), trap) | c <- cs ++ letters d0]
   in DFA {..}

changeState :: (Ord s, Ord c, Hashable s) => (t -> s) -> DFA t c -> DFA s c
changeState f DFA {initial = ini, final = fs, transition = trans} =
  let initial = f ini
      final = HS.map f fs
      transition = M.mapKeys (first f) $ fmap f trans
   in DFA {..}

split ::
  (Ord s, Ord c, Eq s, Hashable s) =>
  DFA s c ->
  (c, HashSet s) ->
  HashSet s ->
  Maybe (HashSet s, HashSet s)
split d (c, b') b =
  let (b0, b1) = partition (maybe False (`HS.member` b') . flip (feed d) c) $ HS.toList b
   in if null b0 || null b1
        then Nothing
        else Just (fromList b0, fromList b1)
{-# INLINE split #-}

partiteDFA :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> [HashSet s]
partiteDFA d@DFA {..}
  | null final || states d == final = [states d]
  | otherwise =
    let (fs, qs) = (final, states d `HS.difference` final)
     in loop [(l, smaller fs qs) | l <- chars] [fs, qs]
  where
    chars = letters d
    loop [] qs = qs
    loop ((a, b') : ws) ps =
      let (ws', ps') = foldr step (ws, []) ps
          step b (wsc, psc) =
            case split d (a, b') b of
              Nothing -> (wsc, b : psc)
              Just (b0, b1) ->
                let refine c ww
                      | (xs, _ : ys) <- {-# SCC "refine/break" #-} break (== (c, b)) ww = {-# SCC "refine/cat" #-} (c, b0) : (c, b1) : xs ++ ys
                      | otherwise = (c, smaller b0 b1) : ww
                 in ({-# SCC "refine/foldr" #-} foldr refine wsc chars, {-# SCC "psupd" #-} [b0, b1] ++ psc)
       in loop ws' ps'

smaller :: HashSet a -> HashSet a -> HashSet a
smaller s t = minimumBy (comparing HS.size) [s, t]

minimize :: (Ord c, Ord q, Hashable q) => DFA q c -> DFA q c
minimize dfa =
  let reps = partiteDFA dfa
   in quotient dfa reps

discardRedundant :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> DFA s c
discardRedundant d@DFA {final = fs, transition = tr, initial} =
  let reachable = fromList (M.keys (walk d))
      final = fs `HS.intersection` reachable
      transition = M.filterWithKey (\(a, _) b -> all (`HS.member` reachable) [a, b]) tr
   in DFA {..}

complement :: (Ord q, Ord c, Hashable q, Eq q) => DFA q c -> DFA q c
complement d@DFA {..} = minimize $ d {final = states d `HS.difference` final}

feed :: (Ord c, Ord q) => DFA q c -> q -> c -> Maybe q
feed DFA {..} q i = M.lookup (q, i) transition
{-# INLINE feed #-}

walk :: (Ord c, Ord q) => DFA q c -> Map q (Seq c)
walk d@DFA {..} = execState (visit S.empty initial) M.empty
  where
    visit !s !q = do
      modify $ M.insert q s
      forM_ (letters d) $ \i -> for (feed d q i) $ \q' -> do
        visited <- gets (M.member q')
        unless visited $ visit (s S.|> i) q'
    {-# INLINE visit #-}
{-# INLINE walk #-}

letters :: Eq a => DFA a1 a -> [a]
letters DFA {transition} = nub $ map snd $ M.keys transition
{-# INLINE letters #-}

changeLetter :: (Ord s, Ord d) => (c -> d) -> DFA s c -> DFA s d
changeLetter f DFA {transition = ts, ..} =
  let transition = M.mapKeys (second f) ts
   in DFA {..}

accepts :: (Ord q, Ord c, Hashable q) => DFA q c -> [c] -> Bool
accepts d@DFA {..} = accepts' d initial

accepts' :: (Ord q, Ord c, Hashable q) => DFA q c -> q -> [c] -> Bool
accepts' d q [] = isFinal d q
accepts' d q (c : cs) =
  case feed d q c of
    Nothing -> False
    Just q' -> accepts' d q' cs

acceptsNFA :: (Ord q, Ord c, Hashable q) => NFA q c -> [c] -> Bool
acceptsNFA d@NFA {..} = acceptsNFA' d initialNFA

acceptsNFA' :: (Ord q, Ord c, Hashable q) => NFA q c -> q -> [c] -> Bool
acceptsNFA' NFA {finalNFA} q [] = q `HS.member` finalNFA
acceptsNFA' d@NFA {transitionNFA} q (c : cs) =
  maybe False (any (\q' -> acceptsNFA' d q' cs)) (M.lookup (q, c) transitionNFA)
