{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}

module Data.Fuzzy
       (
         Fuzzy (..)
       , Grade, MembershipGrade
       , FuzzySet (..)
       , FuzzySetFromList (..)
       , FuzzySetUpdate (..)
       , DGrade
       , MapFuzzySet
       ) where

import           Control.Arrow (first)
import           Data.Map      (Map)
import qualified Data.Map      as Map
import           Data.Maybe    (fromMaybe)

class Fuzzy a where
  infixr 3 ?&
  (?&) :: a -> a -> a
  infixr 2 ?|
  (?|) :: a -> a -> a
  inv :: a -> a

-- TBD: semiring ?
class (Fuzzy a, Ord a, Enum a, Bounded a, Fractional a) => Grade a

type MembershipGrade a g = a -> g

instance Grade g => Fuzzy (MembershipGrade a g) where
  x ?& y = \a -> x a ?& y a
  x ?| y = \a -> x a ?| y a
  inv x = \a -> inv (x a)

class Fuzzy a => FuzzySet a where
  type Value a
  type Degree a
  mu :: a -> Value a -> Degree a
  support :: Eq (Value a) => a -> [Value a]

class FuzzySet s => FuzzySetFromList s where
  fromList :: [(Value s, Degree s)] -> s

class FuzzySet a => FuzzySetUpdate a where
  update :: a -> Value a -> Degree a -> a

newtype DGrade =
  DGrade { unDGrade :: Double }
  deriving (Eq, Ord, Enum)

instance Bounded DGrade where
  minBound = DGrade 0
  maxBound = DGrade 1

checkDGrade :: Double -> Double
checkDGrade x | 0 <= x && x <= 1 = x
              | otherwise        = error "Data.Fuzzy.DGrade: bad argument"

-- normalizeDGrade :: Double -> Double
-- normalizeDGrade x | 0 <= x && x <= 1 = x
--                   | x < 0 = 0
--                   | 1 < x = 1

instance Fuzzy DGrade where
  (DGrade x) ?& (DGrade y) = DGrade (x `min` y)
  (DGrade x) ?| (DGrade y) = DGrade (x `max` y)
  inv (DGrade x) = DGrade (1 - x)

-- only for numeric literal
instance Num DGrade where
  fromInteger = fromRational . fromInteger
--   (DGrade x) + (DGrade y) = DGrade (checkDGrade (x + y))
--   (DGrade x) - (DGrade y) = DGrade (checkDGrade (x - y))

-- only for numeric literal
instance Fractional DGrade where
  fromRational x = DGrade (checkDGrade (fromRational x))

instance Real DGrade where
  toRational  = toRational . unDGrade

instance Show DGrade where
  show = show . unDGrade

instance Read DGrade where
  readsPrec prec = map (first DGrade) . readsPrec prec

instance Grade DGrade

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
-}
newtype MapFuzzySet a d =
  MapFuzzySet (Map a d)
  deriving (Show, Read, Eq, Ord)

instance (Ord a, Show a, Grade d) => Fuzzy (MapFuzzySet a d) where
  (MapFuzzySet x) ?& (MapFuzzySet y) = undefined
--     zs = support x `List.intersect` support y
  (MapFuzzySet x) ?| (MapFuzzySet y) = undefined

instance (Ord a, Show a, Grade d) => FuzzySet (MapFuzzySet a d) where
  type Value (MapFuzzySet a d) = a
  type Degree (MapFuzzySet a d) = d
  mu (MapFuzzySet m) x = fromMaybe minBound (Map.lookup x m)
  support (MapFuzzySet m) = Map.keys m

{-|
-}
instance (Ord a, Show a, Grade g) => FuzzySetFromList (MapFuzzySet a g) where
  fromList xs = MapFuzzySet (Map.fromList xs)

instance (Ord a, Show a, Grade d) => FuzzySetUpdate (MapFuzzySet a d) where
  update (MapFuzzySet m) x g = MapFuzzySet (Map.insert x g m)

-- fromCoreList :: (Ord a, Grade g) => [a] -> MapFuzzySet a g
-- fromCoreList xs = fromList (zip xs (repeat maxBound))

-- support
-- core
-- threshold
