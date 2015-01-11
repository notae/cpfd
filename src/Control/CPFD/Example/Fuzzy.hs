-- Example of fuzzy CSP

module Control.CPFD.Example.Fuzzy where

import Data.Fuzzy

fs1 :: MapFuzzySet Int DGrade
fs1 = fromList [(0, 0.5), (1, 1), (2, 0.5)]

-- Fuzzy Relation

type FuzzyRelation a b g = a -> b -> g
type FuzzyRelation' a b g = (a, b) -> g

fuzzyIntEq :: FuzzyRelation Int Int DGrade
fuzzyIntEq x y = fromRational (toRational g) where
  d = abs (x - y)
  c = 10
  r = fromInteger (toInteger d) / fromInteger (toInteger c)
  g, minB, maxB :: Double
  minB = (fromRational . toRational) (minBound :: DGrade)
  maxB = (fromRational . toRational) (maxBound :: DGrade)
  g = if d < c then maxB - r else minB

-- Fuzzy Constraint

-- type FuzzyArcProp a b =
--   FuzzyRelation a b -> FuzzySet a -> FuzzySet b -> (FuzzySet a, FuzzySet b)
