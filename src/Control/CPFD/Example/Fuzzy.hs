-- Example of fuzzy CSP

{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD.Example.Fuzzy
       (
         fs1, fs2
       , testCons
       , exFCSP
       ) where

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

type FuzzyRelation a b g = Membership (a, b) g

type FuzzyRelation3 a b c g = Membership (a, b, c) g

fuzzyIntEq :: Membership (Int, Int) RGrade
fuzzyIntEq (x, y) = fromRational g where
  d = abs (x - y)
  c = 10
  r = toRational d / toRational c
  g, minB, maxB :: Rational
  minB = toRational (minBound :: RGrade)
  maxB = toRational (maxBound :: RGrade)
  g = if d < c then maxB - r else minB

-- Fuzzy Constraint

dom1, dom2 :: Grade g => MapFuzzySet Int g
dom1 = fromCoreList [0..10]
dom2 = fromCoreList [0..10]

{-|
>>> testCons
7 % 10
-}
testCons :: RGrade
testCons = cons fuzzyIntEq dom1 dom2 2 5

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
exFCSP :: [FC RGrade]
exFCSP = [FC c1, FC c2, FC c3, FC c4]

a0, a1, a2, a3, a4 :: RGrade
[a0, a1, a2, a3, a4] = [0, 0.3, 0.5, fnot a1, 1]

c1 :: FuzzyRelation3 Int Int Int RGrade
c1 (x, y, z) = if x + y + z == 7 then a4 else a0

c2 :: MapFuzzySet Int RGrade
c2 = fromList [(1, a3), (2, 1), (3, a3)]

c3 :: Membership Int RGrade
c3 y | y == 3 || y == 4 = a4
     | otherwise        = a2

c4 :: Membership Int RGrade
c4 x | x == 4           = a4
     | x == 3 || x == 5 = a3
     | otherwise        = a1
