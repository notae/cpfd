{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}

module Data.Fuzzy where

import           Control.Arrow (first)
import qualified Data.List     as List
import           Data.Map      (Map)
import qualified Data.Map      as Map
import           Data.Maybe    (fromMaybe)

class Eq a => Fuzzy a where
  infixr 3 ?&
  (?&) :: a -> a -> a
  infixr 2 ?|
  (?|) :: a -> a -> a
  inv :: a -> a

-- semiring ?
class (Fuzzy a, Ord a, Enum a, Bounded a, Fractional a) => Grade a

class Fuzzy a => FuzzySet a where
  type Value a
  type Degree a
  mu :: a -> Value a -> Degree a
  support :: Eq (Value a) => a -> [Value a]
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

fromList :: Ord a => [(a, d)] -> MapFuzzySet a d
fromList xs = MapFuzzySet (Map.fromList xs)

fromCoreList :: (Ord a, Grade d) => [a] -> MapFuzzySet a d
fromCoreList xs = fromList (zip xs (repeat maxBound))

-- support
-- core
-- threshold
