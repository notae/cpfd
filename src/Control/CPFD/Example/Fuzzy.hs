-- Example of fuzzy CSP

{-# LANGUAGE ConstraintKinds #-}

module Control.CPFD.Example.Fuzzy where

import           Control.Applicative ((<$>), (<*>))
import           Data.Fuzzy
import           Data.List           (foldl')
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Debug.Trace         (traceShow)

fs1 :: MapFuzzySet Int DGrade
fs1 = fromList [(0, 0.5), (1, 1), (2, 0.5)]

fs2 :: MapFuzzySet Int DGrade
fs2 = fromList [(1, 0.5), (2, 0.8), (3, 0.2)]

-- Fuzzy Relation

-- type FuzzyRelationGrade a b g = MembershipGrade (a, b) g

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

frdom :: Set (Int, Int)
frdom = Set.fromList ((,) <$> [0..10] <*> [0..10])

fr :: MFFuzzySet (Int, Int) RGrade
fr = MFFSet fuzzyIntEq frdom

dom1, dom2 :: Grade g => MapFuzzySet Int g
dom1 = fromCoreList [0..10]
dom2 = fromCoreList [0..10]

revise :: (Fuzzy (r (a, b) g), FuzzySet r,
           Fuzzy (s a g), Fuzzy (s b g), FuzzySet s, FuzzySetUpdate s,
           FValue a, FValue b, Grade g) =>
           r (a, b) g -> s a g -> s b g -> g -> (g, Bool, s a g)
revise r x1 x2 sup = (sup', changed, x1') where
  sup' = sup ?& height
  (changed, height, x1') = foldArc (revise0 r x2) (False, minBound, x1) x1 x2

revise0 :: (Fuzzy (r (a, b) g), FuzzySet r,
            Fuzzy (s a g), Fuzzy (s b g), FuzzySet s, FuzzySetUpdate s,
            FValue a, FValue b, Grade g) =>
           r (a, b) g -> s b g -> (Bool, g, s a g) -> (a, b) ->
           (Bool, g, s a g)
-- revise0 r x2 (ch, h, x1) (d1, d2)
--   | traceShow ("revise0", ((d1, d2), h)) False = undefined
revise0 r x2 (ch, h, x1) (d1, d2) = (ch', h', x1') where
  nd = cons r x1 x2 d1 d2
  h' = nd ?| h
  (ch', x1') =
    if nd /= mu x1 d1
    then (True, update x1 d1 nd)
    else (ch,   x1)

foldArc :: (Fuzzy (s a g), FuzzySet s, Ord a, Ord b, Grade g) =>
           (c -> (a, b) -> c) -> c -> s a g -> s b g -> c
foldArc f c x1 x2 = foldl' g c (support x1) where
  g c' d1 = foldl' (\c'' d2 -> f c'' (d1, d2)) c' (support x2)

{-|
>>> cons fr dom1 dom2 2 5
7 % 10
-}
cons :: (Fuzzy (r (a, b) g), FuzzySet r,
         Fuzzy (s a g), Fuzzy (s b g), FuzzySet s,
         Ord a, Ord b, Grade g) =>
        r (a, b) g -> s a g -> s b g -> a -> b -> g
cons r x1 x2 d1 d2 = mu x1 d1 ?& mu r (d1, d2) ?& mu x2 d2
