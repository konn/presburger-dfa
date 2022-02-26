{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module Arithmetic.Presburger.Solver.DFA.Types where

import Control.DeepSeq (NFData (rnf))
import Data.Bit (Bit (Bit))
import Data.Data (Data)
import Data.Typeable (Typeable)
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import GHC.Generics (Generic)

data Ident
  = Ident !String
  | Anonymous !Int
  deriving (Generic, Data, Typeable, Eq, Ord)
  deriving anyclass (NFData)

type Expr mode = Expr' mode Ident

data Expr' mode var where
  Var :: !v -> Expr' mode v
  Num :: !Integer -> Expr' mode v
  (:+) :: !(Expr' m v) -> !(Expr' n v) -> Expr' (Switch m n) v
  (:-) :: !(Expr' m v) -> !(Expr' n v) -> Expr' 'Extended v
  (:*) :: !Integer -> !(Expr' m v) -> Expr' m v

deriving instance Functor (Expr' mode)

deriving instance Foldable (Expr' mode)

deriving instance Traversable (Expr' mode)

type Formula mode = Formula' mode Ident

data Formula' mode var where
  (:<=) :: !(Expr a) -> !(Expr b) -> Formula' (Switch a b) var
  (:==) :: !(Expr a) -> !(Expr b) -> Formula' (Switch a b) var
  (:<) :: !(Expr a) -> !(Expr b) -> Formula' 'Extended var
  (:>=) :: !(Expr a) -> !(Expr b) -> Formula' 'Extended var
  (:>) :: !(Expr a) -> !(Expr b) -> Formula' 'Extended var
  Not :: !(Formula' m var) -> Formula' m var
  (:\/) :: !(Formula' m var) -> !(Formula' n var) -> Formula' (Switch m n) var
  (:/\) :: !(Formula' m var) -> !(Formula' n var) -> Formula' (Switch m n) var
  (:=>) :: !(Formula' m var) -> !(Formula' n var) -> Formula' 'Extended var
  Ex :: !Ident -> !(Formula' m var) -> Formula' m var
  Any :: !Ident -> !(Formula' m var) -> Formula' 'Extended var

deriving instance Functor (Formula' m)

deriving instance Foldable (Formula' m)

deriving instance Traversable (Formula' m)

instance NFData (Expr a) where
  rnf (Var t) = rnf t
  rnf (Num t) = rnf t
  rnf (t1 :+ t2) = rnf t1 `seq` rnf t2
  rnf (t1 :- t2) = rnf t1 `seq` rnf t2
  rnf (t1 :* t2) = rnf t1 `seq` rnf t2

instance NFData v => NFData (Formula' a v) where
  rnf (t1 :<= t2) = rnf t1 `seq` rnf t2
  rnf (t1 :== t2) = rnf t1 `seq` rnf t2
  rnf (t1 :< t2) = rnf t1 `seq` rnf t2
  rnf (t1 :>= t2) = rnf t1 `seq` rnf t2
  rnf (t1 :> t2) = rnf t1 `seq` rnf t2
  rnf (Not t) = rnf t
  rnf (t1 :\/ t2) = rnf t1 `seq` rnf t2
  rnf (t1 :/\ t2) = rnf t1 `seq` rnf t2
  rnf (t1 :=> t2) = rnf t1 `seq` rnf t2
  rnf (Ex t1 t2) = rnf t1 `seq` rnf t2
  rnf (Any t1 t2) = rnf t1 `seq` rnf t2

instance Show Ident where
  show (Ident x) = x
  show (Anonymous i) = "_[" ++ show i ++ "]"

pattern O :: Bit
pattern O = Bit False

pattern I :: Bit
pattern I = Bit True

{-# COMPLETE I, O #-}

data Mode = Raw | Extended
  deriving (Read, Show, Eq, Ord)

type family Switch m n where
  Switch 'Raw m = m
  Switch 'Extended m = 'Extended
  Switch m 'Extended = 'Extended
  Switch a a = a

class Subst f v | f -> v where
  subst :: v -> v -> f m v -> f m v

instance Subst Expr' Ident where
  subst old new (Var e)
    | e == old = Var new
    | otherwise = Var e
  subst _ _ (Num e) = Num e
  subst old new (e1 :+ e2) = subst old new e1 :+ subst old new e2
  subst old new (e1 :- e2) = subst old new e1 :- subst old new e2
  subst old new (e1 :* e2) = e1 :* subst old new e2

instance Subst Expr' Ident => Subst Formula' Ident where
  subst old new (e1 :<= e2) = subst old new e1 :<= subst old new e2
  subst old new (e1 :== e2) = subst old new e1 :== subst old new e2
  subst old new (e1 :< e2) = subst old new e1 :< subst old new e2
  subst old new (e1 :>= e2) = subst old new e1 :>= subst old new e2
  subst old new (e1 :> e2) = subst old new e1 :> subst old new e2
  subst old new (Not e) = Not (subst old new e)
  subst old new (e1 :\/ e2) = subst old new e1 :\/ subst old new e2
  subst old new (e1 :/\ e2) = subst old new e1 :/\ subst old new e2
  subst old new (e1 :=> e2) = subst old new e1 :=> subst old new e2
  subst old new (Ex v e)
    | old == v = Ex v e
    | otherwise = Ex v (subst old new e)
  subst old new (Any v e)
    | old == v = Any v e
    | otherwise = Any v (subst old new e)

instance Show (Expr m) where
  showsPrec _ (Var i) = shows i
  showsPrec d (Num n) = showsPrec d n
  showsPrec d (v1 :+ v2) =
    showParen (d > 8) $
      showsPrec 8 v1 . showString " + " . showsPrec 8 v2
  showsPrec d (v1 :- v2) =
    showParen (d > 8) $
      showsPrec 8 v1 . showString " - " . showsPrec 9 v2
  showsPrec d (n :* v2) =
    showParen (d > 10) $
      showsPrec 10 n . showString " " . showsPrec 10 v2

instance Show (Formula a) where
  showsPrec d (t1 :<= t2) =
    showParen (d > 7) $
      showsPrec 4 t1 . showString " <= " . showsPrec 7 t2
  showsPrec d (t1 :== t2) =
    showParen (d > 7) $
      showsPrec 4 t1 . showString " = " . showsPrec 7 t2
  showsPrec d (t1 :< t2) =
    showParen (d > 7) $
      showsPrec 4 t1 . showString " < " . showsPrec 7 t2
  showsPrec d (t1 :>= t2) =
    showParen (d > 7) $
      showsPrec 4 t1 . showString " >= " . showsPrec 7 t2
  showsPrec d (t1 :> t2) =
    showParen (d > 7) $
      showsPrec 4 t1 . showString " > " . showsPrec 7 t2
  showsPrec d (Not t) =
    showParen (d > 9) $
      showString "~ " . showsPrec 9 t
  showsPrec d (t1 :\/ t2) =
    showParen (d > 2) $ showsPrec 2 t1 . showString " \\/ " . showsPrec 2 t2
  showsPrec d (t1 :/\ t2) =
    showParen (d > 3) $ showsPrec 3 t1 . showString " /\\ " . showsPrec 3 t2
  showsPrec d (t1 :=> t2) =
    showParen (d > 1) $ showsPrec 1 t1 . showString " => " . showsPrec 1 t2
  showsPrec d (Ex i t2) =
    showParen (d > 4) $
      showString "∃ " . shows i . showString ". " . showsPrec 4 t2
  showsPrec d (Any i t2) =
    showParen (d > 4) $
      showString "∀ " . shows i . showString ". " . showsPrec 4 t2

instance Num (Expr a) where
  fromInteger = Num . fromInteger
  (+) = (:+)
  Num n * b = n :* b
  a * Num m = m :* a
  _ * _ = error "At least one of factor must be constant!"
  abs = id
  signum (Num 0) = 0
  signum _ = 1

  negate (Var i) = (-1) :* Var i
  negate (n :* m) = negate n :* m
  negate (Num n) = Num (negate n)
  negate (n :+ m) = negate n :+ negate m
  negate (n :- m) = m :- n

infixl 6 :+, :-

infixr 7 :*

infixr 3 :/\

infixr 2 :\/

infixr 1 :=>

infix 4 :<=, :>=, :<, :>, :==

(.*) :: Num a => a -> Bit -> a
a .* I = a
_ .* O = 0
{-# INLINE (.*) #-}

(.*.) :: (Num a) => V.Vector a -> Bits -> a
(.*.) as = V.sum . V.backpermute as . V.convert . U.elemIndices I

type Bits = U.Vector Bit
