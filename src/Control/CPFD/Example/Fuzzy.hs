-- Example of fuzzy CSP

{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD.Example.Fuzzy where

import           Control.Applicative ((<$>), (<*>))
import           Control.CPFD.Fuzzy
import           Data.Fuzzy
import           Data.List           (foldl')
import           Data.Set            (Set)
import qualified Data.Set            as Set

-- Fuzzy Set

fs1 :: (FValue a, Num a, Grade g) => MapFuzzySet a g
fs1 = fromList [(0, 0.5), (1, 1), (2, 0.5)]

fs2 :: (FValue a, Num a, Grade g) => MapFuzzySet a g
fs2 = fromList [(1, 0.5), (2, 0.8), (3, 0.2)]

-- Fuzzy Relation

type FuzzyRelation a b g = MFFuzzySet (a, b) g
type FuzzyRelationGrade a b g = MembershipGrade (a, b) g

type FuzzyRelation3 a b c g = MFFuzzySet (a, b, c) g
type FuzzyRelationGrade3 a b c g = MembershipGrade (a, b, c) g

fuzzyIntEq' :: MembershipGrade (Int, Int) DGrade
fuzzyIntEq' (x, y) = fromRational (toRational g) where
  iToD = fromInteger . toInteger
  gToD = fromRational . toRational
  d = abs (x - y)
  c = 10
  r = iToD d / iToD c
  g, minB, maxB :: Double
  minB = gToD (minBound :: DGrade)
  maxB = gToD (maxBound :: DGrade)
  g = if d < c then maxB - r else minB

fuzzyIntEq :: MembershipGrade (Int, Int) RGrade
fuzzyIntEq (x, y) = fromRational g where
  d = abs (x - y)
  c = 10
  r = toRational d / toRational c
  g, minB, maxB :: Rational
  minB = toRational (minBound :: RGrade)
  maxB = toRational (maxBound :: RGrade)
  g = if d < c then maxB - r else minB

-- Fuzzy Constraint

-- type FuzzyArcProp a b =
--   FuzzyRelation a b -> FuzzySet a -> FuzzySet b -> (FuzzySet a, FuzzySet b)

frdom :: [(Int, Int)]
frdom = (,) <$> [0..10] <*> [0..10]

fr :: MFFuzzySet (Int, Int) RGrade
fr = mfFuzzySet fuzzyIntEq frdom

dom1, dom2 :: Grade g => MapFuzzySet Int g
dom1 = fromCoreList [0..10]
dom2 = fromCoreList [0..10]

{-|
>>> testCons
7 % 10
-}
testCons :: RGrade
testCons = cons fr dom1 dom2 2 5

-- FCSP Example

{-|
Example from:

> @ARTICLE{Dubois96possibilitytheory,
>     author = {Didier Dubois and Hélène Fargier and Henri Prade},
>     title = {Possibility theory in constraint satisfaction problems: Handling priority, preference and uncertainty},
>     journal = {Applied Intelligence},
>     year = {1996},
>     volume = {6},
>     pages = {287--309}
> }

-}
exFCSP :: [FuzzyRelation3 Int Int Int RGrade]
exFCSP = [c1]

d2 = (,,) <$> d <*> d
d3 = (,,) <$> dx <*> dy <*> dz
[d, dx, dy, dz] = [[0..7], d, d, d]

[a0, a1, a2, a3, a4] = [0, 0.3, 0.5, fnot a1, 1]

-- TBD: domain
c1 :: FuzzyRelation3 Int Int Int RGrade
c1 = mfFuzzySet f d3 where
  f :: FuzzyRelationGrade3 Int Int Int RGrade
  f (x, y, z) = if x + y + z == 7 then maxBound else minBound

c2 :: MapFuzzySet Int RGrade
c2 = fromList [(1, a3), (2, 1), (3, a3)]

c3 :: MFFuzzySet Int RGrade
c3 = mfFuzzySet f dy where
  f :: MembershipGrade Int RGrade
  f y | y == 3 || y == 4 = 1
      | otherwise        = a2

c4 :: MFFuzzySet Int RGrade
c4 = mfFuzzySet f dx where
  f x | x == 4           = 1
      | x == 3 || x == 5 = a3
      | otherwise        = a1
