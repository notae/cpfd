{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Data.Fuzzy
       (
         Fuzzy (..)
       , FValue, Grade, MembershipGrade
       , FuzzySet (..)
       , FuzzySetFromList (..)
       , FuzzySetUpdate (..)
       , DGrade, RGrade
       , MapFuzzySet
       , MFFuzzySet (..)
       ) where

import           Control.Arrow       (first)
import qualified Data.List           as List
import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Data.Maybe          (fromMaybe)
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Text.Show.Functions ()

class Fuzzy a where
  infixr 3 ?&
  (?&) :: a -> a -> a
  infixr 2 ?|
  (?|) :: a -> a -> a
  inv :: a -> a

-- class (Ord v, Show v) => FValue v
type FValue v = (Ord v, Show v)

-- TBD: semiring ?
class (Fuzzy g, Ord g, Enum g, Bounded g, Fractional g, Show g) => Grade g
-- type Grade g = (Fuzzy g, Ord g, Enum g, Bounded g, Fractional g, Show g)

type MembershipGrade a g = a -> g

instance Grade g => Fuzzy (MembershipGrade a g) where
  x ?& y = \a -> x a ?& y a
  x ?| y = \a -> x a ?| y a
  inv x = inv . x

class FuzzySet s where
  mu :: (Fuzzy (s a g), Ord a, Grade g) => s a g -> a -> g
  support :: (Ord a, Grade g) => s a g -> [a]

class FuzzySet s => FuzzySetFromList s where
  fromList :: Ord a => [(a, g)] -> s a g
  fromCoreList :: (Ord a, Grade g) => [a] -> s a g
  fromCoreList xs = fromList (zip xs (repeat maxBound))

class FuzzySet s => FuzzySetUpdate s where
  update :: (Ord a, Grade g) => s a g -> a -> g -> s a g

newtype DGrade =
  DGrade { unDGrade :: Double }
  deriving (Eq, Ord, Enum)

instance Bounded DGrade where
  minBound = DGrade 0
  maxBound = DGrade 1

checkDGrade :: Double -> Double
checkDGrade x | (unDGrade minBound) <= x && x <= (unDGrade maxBound) = x
              | otherwise        = error "Data.Fuzzy.DGrade: bad argument"

instance Fuzzy DGrade where
  (DGrade x) ?& (DGrade y) = DGrade (x `min` y)
  (DGrade x) ?| (DGrade y) = DGrade (x `max` y)
  inv (DGrade x) = DGrade (unDGrade maxBound - x)

-- only for numeric literal
instance Num DGrade where
  fromInteger = fromRational . fromInteger
--   (DGrade x) + (DGrade y) = DGrade (checkDGrade (x + y))
--   (DGrade x) - (DGrade y) = DGrade (checkDGrade (x - y))

-- only for numeric literal
instance Fractional DGrade where
  fromRational = DGrade . checkDGrade . fromRational

instance Real DGrade where
  toRational  = toRational . unDGrade

instance Show DGrade where
  show = show . unDGrade

instance Read DGrade where
  readsPrec prec = map (first DGrade) . readsPrec prec

instance Grade DGrade

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
  inv (RGrade x) = RGrade (unRGrade maxBound - x)

-- only for numeric literal
instance Num RGrade where
  fromInteger = fromRational . fromInteger
--   (RGrade x) + (RGrade y) = RGrade (checkRGrade (x + y))
--   (RGrade x) - (RGrade y) = RGrade (checkRGrade (x - y))

-- only for numeric literal
instance Fractional RGrade where
  fromRational = RGrade . checkRGrade . fromRational

instance Real RGrade where
  toRational  = toRational . unRGrade

instance Show RGrade where
  show = show . unRGrade

instance Read RGrade where
  readsPrec prec = map (first RGrade) . readsPrec prec

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

{-|
>>> let fs1 = fromList [(0, 0.3), (1, 1), (2, 0.7)] :: MapFuzzySet Int DGrade
>>> mu fs1 2
0.7
>>> support fs1
[0,1,2]
>>> update fs1 2 0.6
MapFuzzySet (fromList [(0,0.3),(1,1.0),(2,0.6)])
>>> fromCoreList [0..2] :: MapFuzzySet Int DGrade
MapFuzzySet (fromList [(0,1.0),(1,1.0),(2,1.0)])
-}
newtype MapFuzzySet a d =
  MapFuzzySet (Map a d)
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

-- TBD: domain type for cartesian product D1 x D2 ...
data MFFuzzySet a g =
  MFFSet
  { mf    :: MembershipGrade a g
  , mfDom :: Set a }
  deriving (Show)

instance (Ord a, Grade g) => Fuzzy (MFFuzzySet a g) where
  x ?& y = MFFSet { mf = mf x ?& mf y,
                    mfDom = mfDom x `Set.intersection` mfDom y }
  x ?| y = MFFSet { mf = mf x ?| mf y,
                    mfDom = mfDom x `Set.intersection` mfDom y }
  inv s = s { mf = inv (mf s) }

instance FuzzySet MFFuzzySet where
  mu MFFSet{..} e = if e `Set.member` mfDom then mf e else minBound
  support MFFSet{..} = Set.toList (Set.filter (\e -> mf e > minBound ) mfDom)

-- support
-- core
-- threshold
