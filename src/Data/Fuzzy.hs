{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Data.Fuzzy
       (
       -- * Basic Types
         Fuzzy (..)
       , FValue, Grade
       , Membership
       -- * Fuzzy Set Types
       , FuzzySet (..)
       , FuzzySetFromList (..)
       , FuzzySetUpdate (..)
       , DGrade, RGrade, (%)
       -- * Fuzzy Set Instances
       , MapFuzzySet, (?$)
       , MFFuzzySet, mfFuzzySet
       , MFFuzzySet', mfFuzzySet'
       ) where

import           Control.Arrow       (first)
import qualified Data.List           as List
import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Data.Maybe          (fromMaybe)
import           Data.Ratio          ((%))
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Text.Show.Functions ()

class Fuzzy a where
  -- | And (Intersection)
  infixr 7 ?&
  (?&) :: a -> a -> a
  -- | Or (Union)
  infixr 6 ?|
  (?|) :: a -> a -> a
  -- | Not (Complement)
  fnot :: a -> a

type FValue v = (Ord v, Show v)

-- | Fuzzy grade
-- (TBD: semiring ?)
class (Fuzzy g, Ord g, Enum g, Bounded g, Fractional g, Show g) => Grade g

class FuzzySet s where
  -- | A membership function.
  mu :: (Fuzzy (s a g), Ord a, Grade g) => s a g -> a -> g
  -- | A list of values from the domain for which membership is non-zero.
  support :: (Ord a, Grade g) => s a g -> [a]

class FuzzySet s => FuzzySetFromList s where
  fromList :: (Ord a, Grade g) => [(a, g)] -> s a g
  fromCoreList :: (Ord a, Grade g) => [a] -> s a g
  fromCoreList xs = fromList (zip xs (repeat maxBound))

class FuzzySet s => FuzzySetUpdate s where
  update :: (Ord a, Grade g) => s a g -> a -> g -> s a g

-- | Fuzzy grade based on Double.
newtype DGrade =
  DGrade { unDGrade :: Double }
  deriving (Eq, Ord, Enum)
{-# DEPRECATED DGrade "Use 'Data.Fuzzy.RGrade'" #-}

instance Bounded DGrade where
  minBound = DGrade 0
  maxBound = DGrade 1

checkDGrade :: Double -> Double
checkDGrade x | (unDGrade minBound) <= x && x <= (unDGrade maxBound) = x
              | otherwise        = error "Data.Fuzzy.DGrade: bad argument"

instance Fuzzy DGrade where
  (DGrade x) ?& (DGrade y) = DGrade (x `min` y)
  (DGrade x) ?| (DGrade y) = DGrade (x `max` y)
  fnot (DGrade x) = DGrade (unDGrade maxBound - x)

-- | Only for numeric literals.
instance Num DGrade where
  fromInteger = fromRational . fromInteger
--   (DGrade x) + (DGrade y) = DGrade (checkDGrade (x + y))
--   (DGrade x) - (DGrade y) = DGrade (checkDGrade (x - y))

-- | Only for numeric literals.
instance Fractional DGrade where
  fromRational = DGrade . checkDGrade . fromRational

instance Real DGrade where
  toRational  = toRational . unDGrade

instance Show DGrade where
  show = show . unDGrade

instance Read DGrade where
  readsPrec prec = map (first (DGrade . checkDGrade)) . readsPrec prec

instance Grade DGrade

-- | Fuzzy grade based on Rational.
newtype RGrade =
  RGrade { unRGrade :: Rational }
  deriving (Eq, Ord, Enum)

instance Bounded RGrade where
  minBound = RGrade 0
  maxBound = RGrade 1

checkRGrade :: Rational -> Rational
checkRGrade x | (unRGrade minBound) <= x && x <= (unRGrade maxBound) = x
              | otherwise        = error "Data.Fuzzy.RGrade: bad argument"

instance Fuzzy RGrade where
  (RGrade x) ?& (RGrade y) = RGrade (x `min` y)
  (RGrade x) ?| (RGrade y) = RGrade (x `max` y)
  fnot (RGrade x) = RGrade (unRGrade maxBound - x)

-- | Only for numeric literals.
instance Num RGrade where
  fromInteger = fromRational . fromInteger
--   (RGrade x) + (RGrade y) = RGrade (checkRGrade (x + y))
--   (RGrade x) - (RGrade y) = RGrade (checkRGrade (x - y))

-- | Only for numeric literals.
instance Fractional RGrade where
  fromRational = RGrade . checkRGrade . fromRational

instance Real RGrade where
  toRational  = toRational . unRGrade

instance Show RGrade where
  show = show . unRGrade

instance Read RGrade where
  readsPrec prec = map (first (RGrade . checkRGrade)) . readsPrec prec

instance Grade RGrade

{-
newtype NGrade =
  NGrade { unNGrade :: Int }
  deriving (Eq, Ord, Enum, Show)

instance Bounded NGrade where
  minBound = NGrade 0
  maxBound = NGrade 1

instance Num NGrade where
  fromInteger = NGrade . fromInteger
-}

-- | Fuzzy set based on tuples of value and its membership grade.
{-|
>>> let fs1 = fromList [(0, 0.3), (1, 1), (2, 0.7)] :: MapFuzzySet Int RGrade
>>> mu fs1 2
7 % 10
>>> support fs1
[0,1,2]
>>> update fs1 2 0.6
MapFuzzySet (fromList [(0,3 % 10),(1,1 % 1),(2,3 % 5)])
>>> fromCoreList [0..2] :: MapFuzzySet Int RGrade
MapFuzzySet (fromList [(0,1 % 1),(1,1 % 1),(2,1 % 1)])
-}
newtype MapFuzzySet a g =
  MapFuzzySet (Map a g)
  deriving (Show, Read, Eq, Ord)

instance (Ord a, Grade g) => Fuzzy (MapFuzzySet a g) where
  x ?& y = z where
    zs = support x `List.intersect` support y
    z = fromList (map (\e -> (e, mu x e ?& mu y e)) zs)
  x ?| y = z where
    zs = support x `List.intersect` support y
    z = fromList (map (\e -> (e, mu x e ?| mu y e)) zs)

instance FuzzySet MapFuzzySet where
  mu (MapFuzzySet m) x = fromMaybe minBound (Map.lookup x m)
  support (MapFuzzySet m) = Map.keys m

instance FuzzySetFromList MapFuzzySet where
  fromList xs = MapFuzzySet (Map.fromList xs)

instance FuzzySetUpdate MapFuzzySet where
  update (MapFuzzySet m) x g = MapFuzzySet $
    if g == minBound
    then Map.delete x m
    else Map.insert x g m

infixr 4 ?$
(?$) :: (Ord b, Grade g) => (a -> b) -> MapFuzzySet a g -> MapFuzzySet b g
(?$) f (MapFuzzySet s) = MapFuzzySet (Map.mapKeysWith (?|) f s)

-- | Membership function.
--   This can be regarded as fuzzy set based on membership function.
type Membership a g = a -> g

instance Grade g => Fuzzy (Membership a g) where
  x ?& y = \a -> x a ?& y a
  x ?| y = \a -> x a ?| y a
  fnot x = fnot . x

instance FuzzySet (->) where
  mu f = f
--   support = error "not support"

-- | Wrapped membership function.
newtype MF a g = MF { unMF :: Membership a g } deriving (Show, Fuzzy)
{-# DEPRECATED MF "Use 'Data.Fuzzy.Membership'" #-}

instance FuzzySet MF where
  mu (MF m) = m

-- | Fuzzy set based on membership function and its domain.
--
-- TBD: domain type for cartesian product D1 x D2 ...
data MFFuzzySet a g =
  MFFSet
  { mf    :: Membership a g
  , mfDom :: Set a }
  deriving (Show)
{-# DEPRECATED MFFuzzySet "Use 'Data.Fuzzy.Membership'" #-}

mfFuzzySet :: (Ord a, Grade g) => Membership a g -> [a] -> MFFuzzySet a g
mfFuzzySet f xs = MFFSet f (Set.fromList xs)

instance (Ord a, Grade g) => Fuzzy (MFFuzzySet a g) where
  x ?& y = MFFSet { mf = mf x ?& mf y,
                    mfDom = mfDom x `Set.intersection` mfDom y }
  x ?| y = MFFSet { mf = mf x ?| mf y,
                    mfDom = mfDom x `Set.intersection` mfDom y }
  fnot s = s { mf = fnot (mf s) }

instance FuzzySet MFFuzzySet where
  mu MFFSet{..} e = if e `Set.member` mfDom then mf e else minBound
  support MFFSet{..} = Set.toList (Set.filter (\e -> mf e > minBound ) mfDom)

newtype MFFuzzySet' a g =
  MFFSet'
  { mf' :: Membership a g }
  deriving (Show)
{-# DEPRECATED MFFuzzySet' "Use 'Data.Fuzzy.Membership'" #-}

mfFuzzySet' :: (Ord a, Grade g) => Membership a g -> MFFuzzySet' a g
mfFuzzySet' f = MFFSet' f

instance (Ord a, Grade g) => Fuzzy (MFFuzzySet' a g) where
  x ?& y = MFFSet' { mf' = mf' x ?& mf' y }
  x ?| y = MFFSet' { mf' = mf' x ?| mf' y }
  fnot s = s { mf' = fnot (mf' s) }

instance FuzzySet MFFuzzySet' where
  mu MFFSet'{..} e = mf' e
--   support MFFSet{..} = Set.toList (Set.filter (\e -> mf e > minBound ) mfDom)
