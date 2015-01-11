-- Example of fuzzy CSP

module Control.CPFD.Example.Fuzzy where

import Data.Fuzzy

fs1 :: MapFuzzySet Int DGrade
fs1 = fromList [(0, 0.5), (1, 1), (2, 0.5)]

fs2 :: MapFuzzySet Int DGrade
fs2 = fromList [(1, 0.5), (2, 0.8), (3, 0.2)]

-- Fuzzy Relation

-- type FuzzyRelationGrade a b g = MembershipGrade (a, b) g

fuzzyIntEq :: MembershipGrade (Int, Int) DGrade
fuzzyIntEq (x, y) = fromRational (toRational g) where
  iToD = fromInteger . toInteger
  gToD = fromRational . toRational
  d = abs (x - y)
  c = 10
  r = iToD d / iToD c
  g, minB, maxB :: Double
  minB = gToD (minBound :: DGrade)
  maxB = gToD (maxBound :: DGrade)
  g = if d < c then maxB - r else minB

-- Fuzzy Constraint

-- type FuzzyArcProp a b =
--   FuzzyRelation a b -> FuzzySet a -> FuzzySet b -> (FuzzySet a, FuzzySet b)
