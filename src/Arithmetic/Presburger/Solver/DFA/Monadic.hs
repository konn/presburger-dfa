{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Arithmetic.Presburger.Solver.DFA.Monadic
  ( Expr' (..),
    Expr,
    Formula' (..),
    Formula,
    Validity (..),
    SolverT,
    Solver,
    runSolverT,
    runSolver,
    assume,
    prove,
    currentSolution,
    findSolutionsFor,
  )
where

import Arithmetic.Presburger.Solver.DFA
import Arithmetic.Presburger.Solver.DFA.Automata
import Arithmetic.Presburger.Solver.DFA.Types
import Control.Applicative (Alternative)
import Control.Monad ((<=<))
import Control.Monad.Trans.State.Strict (StateT, evalState, evalStateT, get, gets, modify, put)
import Data.Functor.Identity (Identity)
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as M
import qualified Data.Vector.Unboxed as U

type Letter = Bits

newtype SolverT m a = SolverT {runSolverT_ :: StateT SolverState m a}
  deriving (Monad, Applicative, Functor)

data SolverState = SolverState
  { dfa :: Maybe (DFA MachineState Letter)
  , varsDic :: M.Map Ident Integer
  , varCount :: Integer
  }

type Solver = SolverT Identity

initialState :: SolverState
initialState =
  SolverState
    { dfa = Nothing
    , varsDic = mempty
    , varCount = 0
    }

currentDFA :: Monad m => SolverT m (Maybe (DFA MachineState Letter))
currentDFA = SolverT $ gets dfa

updateVar :: Monad m => Ident -> SolverT m ()
updateVar ident = SolverT $ do
  s@SolverState {..} <- get
  case M.lookup ident varsDic of
    Just _ -> return ()
    Nothing ->
      put $
        s
          { varCount = varCount + 1
          , varsDic = M.insert ident varCount varsDic
          , dfa = padCharLast <$> dfa
          }

padCharLast :: Ord s => DFA s Bits -> DFA s Bits
padCharLast DFA {transition = tr, ..} =
  let transition =
        M.fromList $
          concat
            [ [((q, l `U.snoc` O), p), ((q, l `U.snoc` I), p)]
            | ((q, l), p) <- M.toList tr
            ]
   in DFA {..}
{-# INLINE padCharLast #-}

runSolverT :: Monad m => SolverT m a -> m a
runSolverT s = evalStateT (runSolverT_ s) initialState
{-# INLINE runSolverT #-}

runSolver :: Solver a -> a
runSolver s = evalState (runSolverT_ s) initialState
{-# INLINE runSolver #-}

toDFA :: Monad m => Formula k -> SolverT m (DFA MachineState Bits)
toDFA f = do
  let f' = encode f
  mapM_ updateVar (freeVars f')
  SolverT $ flip buildDFAWith f' <$> gets varsDic
{-# INLINE toDFA #-}

assume :: Monad m => Formula k -> SolverT m ()
assume f = do
  d <- viewWithFormula f
  SolverT $ modify $ \s -> s {dfa = Just d}
{-# INLINE assume #-}

prove :: Monad m => Formula k -> SolverT m Validity
prove f = do
  maybe Proved Refuted <$> findSolutionsFor (Not f)
{-# INLINE prove #-}

currentSolution :: (Alternative f, Monad m) => SolverT m (f Solution)
currentSolution = maybe (return $ pure M.empty) solveDFA =<< currentDFA
{-# INLINE currentSolution #-}

solveDFA :: (Monad m, Ord a, Alternative f, Hashable a) => DFA a Bits -> SolverT m (f Solution)
solveDFA d = SolverT $ gets $ \s -> getDFASolution (varsDic s) d
{-# INLINE solveDFA #-}

viewWithFormula :: Monad m => Formula k -> SolverT m (DFA MachineState Bits)
viewWithFormula f = do
  d <- toDFA f
  maybe d (minimize . intersectionWith pairTrappedState d) <$> currentDFA
{-# INLINE viewWithFormula #-}

findSolutionsFor :: (Alternative f, Monad m) => Formula k -> SolverT m (f Solution)
findSolutionsFor = solveDFA <=< viewWithFormula
{-# INLINE findSolutionsFor #-}
