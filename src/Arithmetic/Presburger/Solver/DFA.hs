{-# LANGUAGE BangPatterns, DataKinds, DeriveDataTypeable, DeriveGeneric    #-}
{-# LANGUAGE FlexibleInstances, GADTs, LambdaCase, NamedFieldPuns          #-}
{-# LANGUAGE NoOverloadedLists, ParallelListComp, PatternGuards, PolyKinds #-}
{-# LANGUAGE RecordWildCards, ScopedTypeVariables, StandaloneDeriving      #-}
{-# LANGUAGE TupleSections, TypeFamilies, TypeOperators, ViewPatterns      #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Arithmetic.Presburger.Solver.DFA where
import           Control.Arrow                    (first, second)
import           Control.Monad                    (filterM, forM_, unless)
import           Control.Monad.Trans.State.Strict (State, execState, get, gets)
import           Control.Monad.Trans.State.Strict (modify, put)
import           Data.Data                        (Data)
import           Data.Either                      (partitionEithers)
import           Data.Foldable                    (toList)
import           Data.Hashable                    (Hashable)
import qualified Data.HashMap.Strict              as HM
import qualified Data.HashSet                     as HS
import           Data.List                        (delete, minimumBy, nub)
import           Data.List                        (partition, sort, transpose)
import           Data.List                        (unfoldr)
import qualified Data.Map.Strict                  as M
import           Data.Maybe                       (fromJust, fromMaybe)
import           Data.Maybe                       (mapMaybe, maybeToList)
import           Data.Monoid                      (First (..))
import           Data.Ord                         (comparing)
import qualified Data.Sequence                    as S
import           Data.Traversable                 (for)
import           Data.Typeable                    (Typeable)
import           Data.Vector                      (Vector)
import qualified Data.Vector                      as V
import           Debug.Trace                      (trace)
import           GHC.Generics                     (Generic)

data Ident = Ident { getIdent :: String }
           | Anonymous { getAnon :: !Int }
           deriving (Generic, Data, Typeable,Eq, Ord)

instance Show Ident where
  show (Ident x) = x
  show (Anonymous i) = "_[" ++ show i ++ "]"

data Bit = O | I
         deriving (Read, Show, Eq, Ord)

data Mode = Raw | Extended
          deriving (Read, Show, Eq, Ord)

type family Switch m n where
  Switch 'Raw m = m
  Switch 'Extended  m = 'Extended
  Switch a a = a

solve :: Formula m -> [M.Map Ident Integer]
solve f =
  let (targ, vdic) = buildDFA $ encode f
      len = M.size vdic
  in map (\sol -> fmap ((sol !!) . fromInteger) vdic) $ getSolution len targ

data Expr mode where
  Var  :: !Ident -> Expr a
  Num  :: !Integer  -> Expr a
  (:+) :: !(Expr m) -> !(Expr n) -> Expr (Switch m n)
  (:-) :: !(Expr m) -> !(Expr n) -> Expr 'Extended
  (:*) :: !Integer  -> !(Expr m) -> Expr m

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

data Formula mode where
  (:<=) :: !(Expr a) -> !(Expr a) -> Formula a
  (:==) :: !(Expr a) -> !(Expr b) -> Formula 'Extended
  (:<)  :: !(Expr a) -> !(Expr b) -> Formula 'Extended
  (:>=) :: !(Expr a) -> !(Expr b) -> Formula 'Extended
  (:>)  :: !(Expr a) -> !(Expr b) -> Formula 'Extended
  Not   :: !(Formula m) -> Formula m
  (:\/) :: !(Formula m) -> !(Formula n) -> Formula 'Extended
  (:/\) :: !(Formula m) -> !(Formula n) -> Formula (Switch m n)
  (:=>) :: !(Formula m) -> !(Formula n) -> Formula 'Extended
  Ex    :: !Ident -> !(Formula m) -> Formula m
  Any   :: !Ident -> !(Formula m) -> Formula 'Extended
deriving instance Show (Formula a)
deriving instance Show (Expr a)

fresh :: Vars f => f a -> Ident
fresh f = Anonymous $ 1 + (maximum $ (-1) : [i | Anonymous i <- vars f])

type Index = Integer
type VarDic = M.Map Ident Integer

buildDFA :: Formula 'Raw -> (DFA Integer Bits, VarDic)
buildDFA f =
  let (_, varDic) = execState (mapM getIdx $ sort (vars f)) (0, M.empty)
  in (buildDFA' varDic f, varDic)

buildDFA' :: VarDic -> Formula 'Raw -> DFA Integer Bits
buildDFA' vdic  (a :<= b) =
  let (nb, pxs) = partitionEithers (summands a)
      (pb, nxs) = partitionEithers (summands b)
      cfs0 = M.unionWith (+) (M.fromList pxs) (fmap negate $ M.fromList nxs)
      ub = sum pb - sum nb
      len = toInteger $ M.size vdic
      cds = map (first (vdic M.!)) $ M.toList cfs0
      cfs = [fromMaybe 0 (lookup i cds) | i <- [0..len-1] ]
  in renumberStates $ atomicToDFA $ Atomic (V.fromList cfs) ub
buildDFA' vdic (Not t) = complement $ buildDFA' vdic t
buildDFA' vdic (t1 :/\ t2) =
  let d1 = buildDFA' vdic (encode t1)
      d2 = buildDFA' vdic (encode t2)
  in renumberStates $ minimize $ d1 `intersection` d2
buildDFA' vdic (Ex v t)
  | v `notElem` vars t = buildDFA' vdic t
  | otherwise =
    let idx = toInteger $ M.size vdic
        var = Anonymous $ 1 + maximum ((-1) : [i | Anonymous i <- M.keys vdic])
        dfa = buildDFA' (M.insert var idx vdic) $ subst v var t
    in changeLetter (uncurry (V.++)) $
       minimize $ renumberStates $ determinize $
       projDFA $ changeLetter (splitNth idx) dfa

class Subst f where
  subst :: Ident -> Ident -> f a -> f a

instance Subst Expr where
  subst old new (Var e)
    | e == old  = Var new
    | otherwise = Var e
  subst _   _   (Num e) = Num e
  subst old new (e1 :+ e2) = subst old new e1 :+ subst old new e2
  subst old new (e1 :- e2) = subst old new e1 :- subst old new e2
  subst old new (e1 :* e2) = e1 :* subst old new e2

instance Subst Formula where
  subst old new (e1 :<= e2) = subst old new e1 :<= subst old new e2
  subst old new (e1 :== e2) = subst old new e1 :== subst old new e2
  subst old new (e1 :< e2)  = subst old new e1 :<  subst old new e2
  subst old new (e1 :>= e2) = subst old new e1 :>= subst old new e2
  subst old new (e1 :> e2)  = subst old new e1 :> subst old new e2
  subst old new (Not e)     = Not (subst old new e)
  subst old new (e1 :\/ e2) = subst old new e1 :\/  subst old new e2
  subst old new (e1 :/\ e2) = subst old new e1 :/\  subst old new e2
  subst old new (e1 :=> e2) = subst old new e1 :=>  subst old new e2
  subst old new (Ex v e)
    | old == v  = Ex v e
    | otherwise = Ex v (subst old new e)
  subst old new (Any v e)
    | old == v  = Any v e
    | otherwise = Any v (subst old new e)

tracing :: Show a => String -> a -> a
tracing lab a = trace (concat [lab, ": ", show a]) a

changeLetter :: (Ord s, Ord d) => (c -> d) -> DFA s c -> DFA s d
changeLetter f DFA{transition = ts, ..} =
  let transition = M.mapKeys (second f) ts
  in DFA{..}

splitNth :: Integer -> Vector a -> ((Vector a, Vector a), a)
splitNth n v =
  let (hd, tl) = V.splitAt (fromInteger n) v
  in ((hd, V.tail tl), V.head tl)

type BuildingEnv = (Index, M.Map Ident Index)

currentLen :: State BuildingEnv Index
currentLen = gets fst

getIdx :: Ident -> State BuildingEnv Index
getIdx ident = gets (M.lookup ident . snd) >>= \case
  Just i -> return i
  Nothing -> do
    (i, dic) <- get
    put (i+1, M.insert ident i dic)
    return i

instance Num (Expr a) where
  fromInteger = Num . fromInteger
  (+) = (:+)
  Num n * b = n :* b
  a * Num m = m :* a
  _ * _     = error "At least one of factor must be constant!"
  abs = id
  signum (Num 0) = 0
  signum _ = 1

  negate (Var i)  = (-1) :* Var i
  negate (n :* m) = negate n :* m
  negate (Num n)  = Num (negate n)
  negate (n :+ m) = negate n :+ negate m
  negate (n :- m) = m :- n

class Encodable f where
  encode :: f m -> f 'Raw

instance Encodable Expr where
  encode (Var v) = Var v
  encode (n :- m) = encode $ n :+ (-1) :* m
  encode (Num i) = Num i
  encode (n :+ m) = encode n :+ encode m
  encode (n :* m) = n :* encode m

infixl 6 :+, :-
infixr 7 :*
infixr 3 :/\
infixr 2 :\/
infixr 1 :=>
infix  4 :<=, :>=, :<, :>, :==

class Vars f where
  vars :: f a -> [Ident]

instance Vars Expr where
  vars (Var v)  = [v]
  vars (a :+ b) = nub $ vars a ++ vars b
  vars (a :- b) = nub $ vars a ++ vars b
  vars (_ :* b) = vars b
  vars (Num _)  = []

instance Vars Formula where
  vars (m1 :<= m2) = nub $ vars m1 ++ vars m2
  vars (m1 :== m2) = nub $ vars m1 ++ vars m2
  vars (m1 :< m2)  = nub $ vars m1 ++ vars m2
  vars (m1 :>= m2) = nub $ vars m1 ++ vars m2
  vars (m1 :> m2)  = nub $ vars m1 ++ vars m2
  vars (Not m)     = vars m
  vars (m1 :\/ m2) = nub $ vars m1 ++ vars m2
  vars (m1 :/\ m2) = nub $ vars m1 ++ vars m2
  vars (m1 :=> m2) = nub $ vars m1 ++ vars m2
  vars (Ex v m)    = delete v $ vars m
  vars (Any v m)   = delete v $ vars m

instance Encodable Formula where
  encode (Not  p)   = Not (encode p)
  encode (p :/\ q)  = encode p :/\ encode q
  encode (p :\/ q)  = Not (Not (encode p) :/\ Not (encode q))
  encode (p :=> q)  = encode $ Not (encode p) :\/ encode q
  encode (Ex   v p) = Ex v (encode p)
  encode (Any  v p) = Not $ Ex v $ Not (encode p)
  encode (n :<= m)  = encode n :<= encode m
  encode (n :>= m)  = encode m :<= encode n
  encode (n :== m)  =
    let (n', m') = (encode n, encode m)
    in encode (n' :<= m' :/\ n' :>= m')
  encode (m :<  n)  =
    let (m', n') = (encode m, encode n)
    in encode $ m' :<= n' :/\ Not (m' :== n')
  encode (m :>  n)  = encode $ n :< m


(.*) :: Integer -> Bit -> Integer
a .* I = a
_ .* O = 0
{-# INLINE (.*) #-}

(.*.) :: Vector Integer -> Vector Bit -> Integer
as .*. bs = V.sum $ V.zipWith (.*) as bs


data Atomic = Atomic { coeffs     :: Vector Integer
                     , upperBound :: Integer
                     }
                deriving (Read, Show, Eq, Ord)

type Bits = Vector Bit

type MachineState  = Integer

states :: (Eq s, Hashable s) => DFA s c -> HS.HashSet s
states DFA{..} = HS.fromList $ initial : concat [[t,s] | ((t, _), s) <- M.toList transition]

data DFA s c = DFA { initial    :: s
                   , final      :: HS.HashSet s
                   , transition :: M.Map (s, c) s
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

atomicToDFA :: Atomic -> DFA MachineState Bits
atomicToDFA Atomic{..} = minimize $ loop [upperBound] HS.empty
                   DFA{ initial = upperBound
                      , transition = M.empty
                      , final = HS.empty
                      }
  where
    inputs = V.replicateM (V.length coeffs) [O, I]
    loop [] _ dfa = dfa
    loop (q : qs) seen d =
      let (dfa', seen', qs') = foldr step (d, seen, qs) inputs
      in loop qs' seen'  dfa'
      where
        step i (DFA{..}, sn, ps) =
          let j = (q - (coeffs .*. i))`div` 2
              ps' | HS.member j sn = ps
                  | otherwise = j : ps
              fs  | j >= 0 = HS.insert j final
                  | otherwise = final
          in (DFA{ transition = M.insert (q, i) j transition
                 , final = fs
                 , ..}, HS.insert j sn, ps')

bitToInt :: Bit -> Integer
bitToInt O = 0
bitToInt I = 1
{-# INLINE bitToInt #-}

newtype PathTable
  = PathTable { pathTable :: HM.HashMap MachineState (HM.HashMap MachineState (S.Seq Bits)) }

decodeSolution :: Int -> [Vector Bit] -> [Integer]
decodeSolution len vs
  | null vs = replicate len 0
  | otherwise = map (foldr (\a b -> bitToInt a + 2*b) 0) $ transpose $ map V.toList vs

getElem :: Foldable t =>  t a -> a
getElem = fromJust . getFirst . foldMap (First . Just)

walk :: (Ord c, Ord q) => DFA q c -> M.Map q (S.Seq c)
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

getSolution :: (Ord a, Hashable a) => Int -> DFA a (Vector Bit) -> [[Integer]]
getSolution l dfa =
  let ss = walk dfa
  in map (decodeSolution l . toList . snd) $ M.toList $
     M.filterWithKey (\k _ -> isFinal dfa k) ss

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

groupByValue :: (Ord a, Eq v) => M.Map a v -> M.Map a a
groupByValue dic
    | Just ((k, v), xs) <- M.minViewWithKey dic
    = let (d0, rest) = M.partition (== v) xs
      in M.insert k k $ fmap (const k) d0 `M.union` groupByValue rest
    | otherwise = M.empty

complement :: (Ord q, Ord c, Hashable q, Eq q) => DFA q c -> DFA q c
complement d@DFA{..} = minimize $ d { final = states d `HS.difference`  final }

feed :: (Ord c, Ord q) => DFA q c -> q -> c -> Maybe q
feed DFA{..} q i =
  M.lookup (q, i) transition

data NFA s c = NFA { initialNFA    :: s
                   , finalNFA      :: HS.HashSet s
                   , transitionNFA :: M.Map (s, c) (HS.HashSet s)
                   } deriving (Show, Eq)



projDFA :: (Ord a, Ord s, Hashable s) => DFA s (a, b) -> NFA s a
projDFA DFA{..} =
  let finalNFA      = final
      initialNFA    = initial
      transitionNFA = M.mapKeysWith HS.union (\(s, l) -> (s, fst l)) $
                      fmap HS.singleton transition
  in NFA{..}

dropNth :: Int -> Vector a -> Vector a
dropNth n v =
  let (vs, us) = V.splitAt n v
  in vs V.++ V.drop 1 us

renumberStates :: (Enum s, Eq a, Num s, Ord s, Ord c, Hashable a, Hashable s) => DFA a c -> DFA s c
renumberStates dfa@DFA{initial = ini, final = fs, transition = trans} =
  let ss = states dfa
      idxDic = HM.fromList $ zip (HS.toList $ HS.insert ini ss) [0..]
      initial = idxDic HM.! ini
      final   = HS.map (idxDic HM.!) $ fs `HS.intersection` HS.insert ini ss
      transition = M.mapKeys (first (idxDic HM.!)) $ fmap (idxDic HM.!) trans
  in DFA{..}

statesNFA :: (Eq a, Hashable a) => NFA a t -> HS.HashSet a
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

{-
transition :: Atomic -> MachineState -> Bits -> MachineState
transition Atomic{..} q c = MachineState $ (getMachineState q - (coeffs .*. c)) `div` 2
-}

quotient :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> [HS.HashSet s] -> DFA s c
quotient DFA{initial = ini, final = fs, transition = tr} (filter (not . HS.null) -> reps) =
  let dic = HM.fromList [(s, getElem r) | r <- reps, s <- HS.toList r]
      look v = fromMaybe v $ HM.lookup v dic
      initial = look ini
      final = HS.map look fs
      transition = M.mapKeys (first look) $ fmap look tr
  in DFA{..}

partiteDFA :: (Ord s, Ord c, Eq s, Hashable s) => DFA s c -> [HS.HashSet s]
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

smaller :: HS.HashSet a -> HS.HashSet a -> HS.HashSet a
smaller s t = minimumBy (comparing HS.size) [s, t]

combinations :: [b] -> [(b, b)]
combinations =
  concat . unfoldr (\case { [] -> Nothing ; (a: as) -> Just (zip (repeat a) as, as)})

