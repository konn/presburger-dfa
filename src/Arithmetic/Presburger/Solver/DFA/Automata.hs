{-# LANGUAGE BangPatterns, NamedFieldPuns, ParallelListComp #-}
{-# LANGUAGE RecordWildCards, ViewPatterns                  #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Arithmetic.Presburger.Solver.DFA.Automata where

import           Control.Arrow                    (first)
import           Control.Arrow                    (second)
import           Control.Monad                    (forM_)
import           Control.Monad                    (unless)
import           Control.Monad                    (filterM)
import           Control.Monad.Trans.State.Strict (execState)
import           Control.Monad.Trans.State.Strict (modify)
import           Control.Monad.Trans.State.Strict (gets)
import           Data.Foldable                    (minimumBy)
import           Data.Foldable                    (toList)
import           Data.Hashable                    (Hashable)
import qualified Data.HashMap.Strict              as HM
import           Data.HashSet                     (HashSet)
import qualified Data.HashSet                     as HS
import           Data.List                        (nub)
import           Data.List                        (partition)
import           Data.List                        (sort)
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as M
import           Data.Maybe                       (fromMaybe)
import           Data.Maybe                       (maybeToList)
import           Data.Maybe                       (mapMaybe)
import           Data.Maybe                       (fromJust)
import           Data.Monoid                      (getFirst)
import           Data.Monoid                      (First (..))
import           Data.Ord                         (comparing)
import           Data.Sequence                    (Seq)
import qualified Data.Sequence                    as S
import           Data.Traversable                 (for)

states :: (Eq s, Hashable s) => DFA s c -> HashSet s
states DFA{..} = HS.fromList $ initial : concat [[t,s] | ((t, _), s) <- M.toList transition]

data DFA s c = DFA { initial    :: s
                   , final      :: HashSet s
                   , transition :: Map (s, c) s
                   } deriving (Show, Eq)

isFinal :: (Eq a, Hashable a) => DFA a c -> a -> Bool
isFinal DFA{..} q = q `HS.member` final

intersection :: (Eq c, Ord c, Hashable a, Hashable b, Ord a, Ord b) => DFA a c -> DFA b c -> DFA Integer c
intersection d1 d2 =
  let ss = HS.fromList [(s, t)
           | s <- HS.toList (states d1)
           , t <- HS.toList (states d2)
           ]
      dic = HM.fromList [(st, i) | st <- HS.toList ss | i <- [0..]]
      inputs = nub $ map snd (M.keys $ transition d1) ++ map snd (M.keys $ transition d2)
      trans = M.fromList [ ((dic HM.! (s, t), l), dic HM.! (s', t'))
                         | l <- inputs
                         , (s, t) <- HS.toList ss
                         , s' <- maybeToList (feed d1 s l)
                         , t' <- maybeToList (feed d2 t l)
                         ]
      fs = HS.fromList [dic HM.!(s, t) | s <- HS.toList (final d1)
                                       , t <- HS.toList (final d2)]
  in DFA{ initial = dic HM.! (initial d1, initial d2)
                 , transition = trans
                 , final = fs
                 }

join :: (Eq c, Ord c, Hashable a, Hashable b, Ord a, Ord b) => DFA a c -> DFA b c -> DFA Integer c
join d1 d2 =
  let ss = HS.fromList [(s, t)
           | s <- HS.toList (states d1)
           , t <- HS.toList (states d2)
           ]
      dic = HM.fromList [(st, i) | st <- HS.toList ss | i <- [0..]]
      inputs = nub $ map snd (M.keys $ transition d1) ++ map snd (M.keys $ transition d2)
      trans = M.fromList [ ((dic HM.! (s, t), l), dic HM.! (s', t'))
                         | l <- inputs
                         , (s, t) <- HS.toList ss
                         , s' <- maybeToList (feed d1 s l)
                         , t' <- maybeToList (feed d2 t l)
                         ]
      fs = HS.fromList $
           [dic HM.! (s, t) | (s, t) <- HS.toList ss
                            , isFinal d1 s || isFinal d2 t]
  in DFA{ initial = dic HM.! (initial d1, initial d2)
                 , transition = trans
                 , final = fs
                 }

data NFA s c = NFA { initialNFA    :: s
                   , finalNFA      :: HashSet s
                   , transitionNFA :: Map (s, c) (HashSet s)
                   } deriving (Show, Eq)



projDFA :: (Ord a, Ord s, Hashable s) => DFA s (a, b) -> NFA s a
projDFA DFA{..} =
  let finalNFA      = final
      initialNFA    = initial
      transitionNFA = M.mapKeysWith HS.union (\(s, l) -> (s, fst l)) $
                      fmap HS.singleton transition
  in NFA{..}

renumberStates :: (Enum s, Eq a, Num s, Ord s, Ord c, Hashable a, Hashable s) => DFA a c -> DFA s c
renumberStates dfa@DFA{initial = ini, final = fs, transition = trans} =
  let ss = states dfa
      idxDic = HM.fromList $ zip (HS.toList $ HS.insert ini ss) [0..]
      initial = idxDic HM.! ini
      final   = HS.map (idxDic HM.!) $ fs `HS.intersection` HS.insert ini ss
      transition = M.mapKeys (first (idxDic HM.!)) $ fmap (idxDic HM.!) trans
  in DFA{..}

statesNFA :: (Eq a, Hashable a) => NFA a t -> HashSet a
statesNFA NFA{..} = HS.fromList $ initialNFA : concat [t : HS.toList s | ((t, _), s) <- M.toList transitionNFA]

-- | Naive Subset construction
determinize :: (Ord c, Eq s, Hashable s, Ord s) => NFA s c -> DFA [s] c
determinize n@NFA{..} =
  let sts  = HS.fromList $ map sort $ filterM (const [True, False]) $ HS.toList $ statesNFA n
      final   = HS.filter (any (`HS.member` finalNFA)) sts
      initial = [initialNFA]
      inputs  = nub $ map snd $ M.keys transitionNFA
      transition = M.fromList [((ss, l), nub $ sort $ concat $ mapMaybe (\s -> HS.toList <$> M.lookup (s, l) transitionNFA) $
                                         ss)
                              | ss <- HS.toList sts
                              , l <- inputs
                              ]
  in DFA{..}

getElem :: Foldable t =>  t a -> a
getElem = fromJust . getFirst . foldMap (First . Just)

quotient :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> [HashSet s] -> DFA s c
quotient DFA{initial = ini, final = fs, transition = tr} (filter (not . HS.null) -> reps) =
  let dic = HM.fromList [(s, getElem r) | r <- reps, s <- HS.toList r]
      look v = fromMaybe v $ HM.lookup v dic
      initial = look ini
      final = HS.map look fs
      transition = M.mapKeys (first look) $ fmap look tr
  in DFA{..}

partiteDFA :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> [HashSet s]
partiteDFA d@DFA{..}
  | null final || states d == final = [states d]
  | otherwise =
    let (fs, qs) = (final, states d `HS.difference` final)
    in loop [(l, smaller fs qs) | l <- chars] [fs, qs]
  where
    chars = letters d
    split (c, b') b =
      let (b0, b1) = partition (maybe False (flip HS.member b') . flip (feed d) c) $ toList b
      in if null b0 || null b1
      then Nothing
      else Just (HS.fromList b0, HS.fromList b1)
    loop [] qs = qs
    loop ((a, b') : ws) ps =
      let (ws', ps') = foldr step (ws, []) ps
          step b (wsc, psc) =
            case split (a, b') b of
              Nothing       -> (wsc, b : psc)
              Just (b0, b1) ->
                let refine c ww
                      | (xs, _ : ys) <- break (== (c, b)) ww = (c, b0) : (c, b1) : xs ++ ys
                      | otherwise = (c, smaller b0 b1)  : ww
                in (foldr refine wsc chars, [b0, b1])
      in loop ws' (ps')

smaller :: HashSet a -> HashSet a -> HashSet a
smaller s t = minimumBy (comparing HS.size) [s, t]
minimize :: (Ord c, Ord q, Hashable q) => DFA q c -> DFA q c
minimize dfa =
  let reps = partiteDFA dfa
  in discardRedundant $ quotient dfa reps

discardRedundant :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> DFA s c
discardRedundant d@DFA{final = fs, transition = tr, initial} =
  let reachable = HS.fromList (M.keys (walk d))
      final = fs `HS.intersection` reachable
      transition = M.filterWithKey (\(a, _) b -> all (`HS.member` reachable) [a, b]) tr
  in DFA{..}

complement :: (Ord q, Ord c, Hashable q, Eq q) => DFA q c -> DFA q c
complement d@DFA{..} = minimize $ d { final = states d `HS.difference`  final }

feed :: (Ord c, Ord q) => DFA q c -> q -> c -> Maybe q
feed DFA{..} q i =
  M.lookup (q, i) transition

walk :: (Ord c, Ord q) => DFA q c -> Map q (Seq c)
walk d@DFA{..} = execState (visit S.empty initial) M.empty
  where
    visit !s !q = do
      modify $ M.insert q s
      forM_ (letters d) $ \i -> for (feed d q i) $ \q' -> do
        visited <- gets (M.member q')
        unless visited $ visit (s S.|> i) q'
    {-# INLINE visit #-}
{-# INLINE walk #-}

letters :: Eq a => DFA a1 a -> [a]
letters DFA{transition} = nub $ map snd $ M.keys transition
{-# INLINE letters #-}

changeLetter :: (Ord s, Ord d) => (c -> d) -> DFA s c -> DFA s d
changeLetter f DFA{transition = ts, ..} =
  let transition = M.mapKeys (second f) ts
  in DFA{..}

