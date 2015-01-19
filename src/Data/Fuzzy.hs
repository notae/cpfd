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
       , FSet (..)
       , FSetFromList (..)
       , FSetApply (..)
       , FSetUpdate (..)
       , DGrade, RGrade, (%)
       -- * Fuzzy Set Instances
       , MapFSet
       , MFFSet, mfFSet
       , MFFSet', mfFSet'
       -- * Type Synonyms
       , FS, FR, FR1, FR2, FR3, FRN
       -- * Map (re-export only type)
       , Map
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

class FSet s where
  -- | A membership function.
  mu :: (Fuzzy (s a g), Ord a, Grade g) => s a g -> a -> g
  -- | A list of values from the domain for which membership is non-zero.
  support :: (Ord a, Grade g) => s a g -> [a]
  size :: (Ord a, Grade g) => s a g -> Int
  size = length . support

class FSet s => FSetFromList s where
  fromList :: (Ord a, Grade g) => [(a, g)] -> s a g
  fromCoreList :: (Ord a, Grade g) => [a] -> s a g
  fromCoreList xs = fromList (zip xs (repeat maxBound))

class FSet s => FSetApply s where
  infixr 4 ?$
  (?$) :: (Ord b, Grade g) => (a -> b) -> s a g -> s b g

class FSet s => FSetUpdate s where
  update :: (Ord a, Grade g) => s a g -> a -> g -> s a g

-- | Fuzzy grade based on 'Double'.
newtype DGrade =
  DGrade { unDGrade :: Double }
  deriving (Eq, Ord, Enum)
{-# DEPRECATED DGrade "Use 'Data.Fuzzy.RGrade'" #-}

instance Bounded DGrade where
  minBound = DGrade 0
  maxBound = DGrade 1

checkDGrade :: Double -> Double
checkDGrade x | (unDGrade minBound) <= x && x <= (unDGrade maxBound) = x
              | otherwise = error "Data.Fuzzy.DGrade: bad argument"

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

-- | Fuzzy grade based on 'Rational'.
newtype RGrade =
  RGrade { unRGrade :: Rational }
  deriving (Eq, Ord, Enum)

instance Bounded RGrade where
  minBound = RGrade 0
  maxBound = RGrade 1

checkRGrade :: Rational -> Rational
checkRGrade x | (unRGrade minBound) <= x && x <= (unRGrade maxBound) = x
              | otherwise = error "Data.Fuzzy.RGrade: bad argument"

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
>>> let fs1 = fromList [(0, 0.3), (1, 1), (2, 0.7)] :: MapFSet Int RGrade
>>> mu fs1 2
7 % 10
>>> support fs1
[0,1,2]
>>> update fs1 2 0.6
MapFSet (fromList [(0,3 % 10),(1,1 % 1),(2,3 % 5)])
>>> fromCoreList [0..2] :: MapFSet Int RGrade
MapFSet (fromList [(0,1 % 1),(1,1 % 1),(2,1 % 1)])
-}
newtype MapFSet a g =
  MapFSet (Map a g)
  deriving (Show, Read, Eq, Ord)

instance (Ord a, Grade g) => Fuzzy (MapFSet a g) where
  x ?& y = z where
    zs = support x `List.intersect` support y
    z = fromList (map (\e -> (e, mu x e ?& mu y e)) zs)
  x ?| y = z where
    zs = support x `List.intersect` support y
    z = fromList (map (\e -> (e, mu x e ?| mu y e)) zs)

instance FSet MapFSet where
  mu (MapFSet m) x = fromMaybe minBound (Map.lookup x m)
  support (MapFSet m) = Map.keys m

instance FSetFromList MapFSet where
  fromList xs = MapFSet (Map.fromList xs)

instance FSetApply MapFSet where
   f ?$ (MapFSet s) = MapFSet (Map.mapKeysWith (?|) f s)

instance FSetUpdate MapFSet where
  update (MapFSet m) x g = MapFSet $
    if g == minBound
    then Map.delete x m
    else Map.insert x g m

-- Fuzzy set based on Map

instance (Ord a, Grade g) => Fuzzy (Map a g) where
  x ?& y = z where
    zs = support x `List.intersect` support y
    z = fromList (map (\e -> (e, mu x e ?& mu y e)) zs)
  x ?| y = z where
    zs = support x `List.intersect` support y
    z = fromList (map (\e -> (e, mu x e ?| mu y e)) zs)

instance FSet Map where
  mu m x = fromMaybe minBound (Map.lookup x m)
  support = Map.keys

instance FSetFromList Map where
  fromList = Map.fromList

instance FSetApply Map where
   f ?$ s = Map.mapKeysWith (?|) f s

instance FSetUpdate Map where
  update m x g =
    if g == minBound
    then Map.delete x m
    else Map.insert x g m

-- | Membership function.
--   This can be regarded as fuzzy set based on membership function.
type Membership a g = a -> g

instance Grade g => Fuzzy (Membership a g) where
  x ?& y = \a -> x a ?& y a
  x ?| y = \a -> x a ?| y a
  fnot x = fnot . x

instance FSet (->) where
  mu f = f
--   support = error "not support"

instance FSetApply (->) where
--    f ?$ s = Map.mapKeysWith (?|) f s

-- | Wrapped membership function.
newtype MF a g = MF { unMF :: Membership a g } deriving (Show, Fuzzy)
{-# DEPRECATED MF "Use 'Data.Fuzzy.Membership'" #-}

instance FSet MF where
  mu (MF m) = m

-- | Fuzzy set based on membership function and its domain.
--
data MFFSet a g =
  MFFSet
  { mf    :: Membership a g
  , mfDom :: Set a }
  deriving (Show)
{-# DEPRECATED MFFSet "Use 'Data.Fuzzy.Membership'" #-}

mfFSet :: (Ord a, Grade g) => Membership a g -> [a] -> MFFSet a g
mfFSet f xs = MFFSet f (Set.fromList xs)

instance (Ord a, Grade g) => Fuzzy (MFFSet a g) where
  x ?& y = MFFSet { mf = mf x ?& mf y,
                    mfDom = mfDom x `Set.intersection` mfDom y }
  x ?| y = MFFSet { mf = mf x ?| mf y,
                    mfDom = mfDom x `Set.intersection` mfDom y }
  fnot s = s { mf = fnot (mf s) }

instance FSet MFFSet where
  mu MFFSet{..} e = if e `Set.member` mfDom then mf e else minBound
  support MFFSet{..} = Set.toList (Set.filter (\e -> mf e > minBound ) mfDom)

newtype MFFSet' a g =
  MFFSet'
  { mf' :: Membership a g }
  deriving (Show)
{-# DEPRECATED MFFSet' "Use 'Data.Fuzzy.Membership'" #-}

mfFSet' :: (Ord a, Grade g) => Membership a g -> MFFSet' a g
mfFSet' f = MFFSet' f

instance (Ord a, Grade g) => Fuzzy (MFFSet' a g) where
  x ?& y = MFFSet' { mf' = mf' x ?& mf' y }
  x ?| y = MFFSet' { mf' = mf' x ?| mf' y }
  fnot s = s { mf' = fnot (mf' s) }

instance FSet MFFSet' where
  mu MFFSet'{..} e = mf' e
--   support MFFSet{..} = Set.toList (Set.filter (\e -> mf e > minBound ) mfDom)

-- Type synonyms

-- | Fuzzy set
type FS a g = Map a g

-- | Fuzzy binary (arc) relation with single type
type FR a g = Membership (a, a) g

-- | Fuzzy unary relation
type FR1 a g = Membership a g

-- | Fuzzy binary (arc) relation
type FR2 a b g = Membership (a, b) g

-- | Fuzzy ternary relation
type FR3 a b c g = Membership (a, b, c) g

-- | Fuzzy n-ary (hyper-arc) relation with single type
type FRN a g = Membership [a] g
