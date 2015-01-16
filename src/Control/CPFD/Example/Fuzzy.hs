-- Example of fuzzy CSP

{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD.Example.Fuzzy
       (
         fs1, fs2
       , testCons
       , exFCSP
       ) where

import Control.CPFD.Fuzzy
import Data.Fuzzy

-- Fuzzy Set

fs1 :: (FValue a, Num a, Grade g) => MapFSet a g
fs1 = fromList [(0, 0.5), (1, 1), (2, 0.5)]

fs2 :: (FValue a, Num a, Grade g) => MapFSet a g
fs2 = fromList [(1, 0.5), (2, 0.8), (3, 0.2)]

{-|
>>> fs3 :: MapFSet Int RGrade
MapFSet (fromList [(1,3 % 10),(2,1 % 1),(3,7 % 10)])
>>> fs3 :: Map Int RGrade
fromList [(1,3 % 10),(2,1 % 1),(3,7 % 10)]
-}
fs3 :: (FSetFromList s, FValue a, Num a, Grade g) => s a g
fs3 = fromList [(1, 0.3), (2, 1), (3, 0.7)]

-- Fuzzy Relation

fuzzyIntEq :: FR Int RGrade
fuzzyIntEq (x, y) = fromRational g where
  d = abs (x - y)
  c = 10
  r = toRational d / toRational c
  g, minB, maxB :: Rational
  minB = toRational (minBound :: RGrade)
  maxB = toRational (maxBound :: RGrade)
  g = if d < c then maxB - r else minB

-- Fuzzy Constraint

dom1, dom2 :: Grade g => Map Int g
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

c1 :: FR3 Int Int Int RGrade
c1 (x, y, z) = if x + y + z == 7 then a4 else a0

c2 :: FS Int RGrade
c2 = fromList [(1, a3), (2, 1), (3, a3)]

c3 :: FR1 Int RGrade
c3 y | y == 3 || y == 4 = a4
     | otherwise        = a2

c4 :: FR1 Int RGrade
c4 x | x == 4           = a4
     | x == 3 || x == 5 = a3
     | otherwise        = a1
