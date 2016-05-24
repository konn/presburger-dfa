{-# LANGUAGE BangPatterns, DataKinds, DeriveDataTypeable, DeriveGeneric    #-}
{-# LANGUAGE FlexibleInstances, GADTs, LambdaCase, NamedFieldPuns          #-}
{-# LANGUAGE NoOverloadedLists, ParallelListComp, PatternGuards, PolyKinds #-}
{-# LANGUAGE RecordWildCards, ScopedTypeVariables, StandaloneDeriving      #-}
{-# LANGUAGE TupleSections, TypeFamilies, TypeOperators, ViewPatterns      #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Arithmetic.Presburger.Solver.DFA.Types where
import           Data.Data     (Data)
import           Data.List     (nub)
import           Data.List     (delete)
import           Data.Typeable (Typeable)
import           Data.Vector   (Vector)
import qualified Data.Vector   as V
import           GHC.Generics  (Generic)

data Ident = Ident !String
           | Anonymous !Int
           deriving (Generic, Data, Typeable,Eq, Ord)


data Expr mode where
  Var  :: !Ident -> Expr a
  Num  :: !Integer  -> Expr a
  (:+) :: !(Expr m) -> !(Expr n) -> Expr (Switch m n)
  (:-) :: !(Expr m) -> !(Expr n) -> Expr 'Extended
  (:*) :: !Integer  -> !(Expr m) -> Expr m


data Formula mode where
  (:<=) :: !(Expr a) -> !(Expr b) -> Formula (Switch a b)
  (:==) :: !(Expr a) -> !(Expr b) -> Formula (Switch a b)
  (:<)  :: !(Expr a) -> !(Expr b) -> Formula 'Extended
  (:>=) :: !(Expr a) -> !(Expr b) -> Formula 'Extended
  (:>)  :: !(Expr a) -> !(Expr b) -> Formula 'Extended
  Not   :: !(Formula m) -> Formula m
  (:\/) :: !(Formula m) -> !(Formula n) -> Formula (Switch m n)
  (:/\) :: !(Formula m) -> !(Formula n) -> Formula (Switch m n)
  (:=>) :: !(Formula m) -> !(Formula n) -> Formula 'Extended
  Ex    :: !Ident -> !(Formula m) -> Formula m
  Any   :: !Ident -> !(Formula m) -> Formula 'Extended

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
  Switch m 'Extended  = 'Extended
  Switch a a = a

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


instance Show (Expr m) where
  showsPrec _ (Var i)    = shows i
  showsPrec d (Num n)    = showsPrec d n
  showsPrec d (v1 :+ v2) = showParen (d > 8) $
    showsPrec 8 v1 . showString " + " . showsPrec 8 v2
  showsPrec d (v1 :- v2) =
    showParen (d > 8) $
    showsPrec 8 v1 . showString " - " . showsPrec 9 v2
  showsPrec d (n :* v2) =
    showParen (d > 10) $
    showsPrec 10 n . showString " " . showsPrec 10 v2

instance Show (Formula a) where
  showsPrec d (t1 :<= t2) = showParen (d > 7) $
    showsPrec 4 t1 . showString " <= " . showsPrec 7 t2
  showsPrec d (t1 :== t2) = showParen (d > 7) $
    showsPrec 4 t1 . showString " = " . showsPrec 7 t2
  showsPrec d (t1 :< t2) = showParen (d > 7) $
    showsPrec 4 t1 . showString " < " . showsPrec 7 t2
  showsPrec d (t1 :>= t2) = showParen (d > 7) $
    showsPrec 4 t1 . showString " >= " . showsPrec 7 t2
  showsPrec d (t1 :> t2) = showParen (d > 7) $
    showsPrec 4 t1 . showString " > " . showsPrec 7 t2
  showsPrec d (Not t) = showParen (d > 9) $
    showString "~ " . showsPrec 9 t
  showsPrec d (t1 :\/ t2) =
    showParen (d > 2) $ showsPrec 2 t1 . showString " \\/ " . showsPrec 2 t2
  showsPrec d (t1 :/\ t2) =
    showParen (d > 3) $ showsPrec 3 t1 . showString " /\\ " . showsPrec 3 t2
  showsPrec d (t1 :=> t2) =
    showParen (d > 1) $ showsPrec 1 t1 . showString " => " . showsPrec 1 t2
  showsPrec d (Ex i t2) = showParen (d > 4) $
    showString "∃ " . shows i . showString ". " . showsPrec 4 t2
  showsPrec d (Any i t2) = showParen (d > 4) $
    showString "∀ " . shows i . showString ". " . showsPrec 4 t2


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

infixl 6 :+, :-
infixr 7 :*
infixr 3 :/\
infixr 2 :\/
infixr 1 :=>
infix  4 :<=, :>=, :<, :>, :==

(.*) :: Num a => a -> Bit -> a
a .* I = a
_ .* O = 0
{-# INLINE (.*) #-}

(.*.) :: Num a => Vector a -> Vector Bit -> a
as .*. bs = V.sum $ V.zipWith (.*) as bs

type Bits = Vector Bit

