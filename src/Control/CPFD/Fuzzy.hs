-- | Fuzzy Constraint Satisfaction Problem Solver

{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE UndecidableInstances      #-}

module Control.CPFD.Fuzzy
       (
         FS, FR, FR1, FC (..), cons
       ) where

import Data.List   (foldl')
import Debug.Trace (traceShow)

import Data.Fuzzy

-- Types

type FS a = MapFuzzySet a RGrade
type FR a b = Membership (a, b) RGrade
type FR1 a = Membership (a, a) RGrade

data FC g = forall s a. (FuzzySet s, Show (s a g)) => FC (s a g)
deriving instance Show (FC g)

-- FCSP Solver

-- solve ::

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

cons :: (Fuzzy (r (a, b) g), FuzzySet r,
         Fuzzy (s a g), Fuzzy (s b g), FuzzySet s,
         Ord a, Ord b, Grade g) =>
        r (a, b) g -> s a g -> s b g -> a -> b -> g
cons r x1 x2 d1 d2 = mu x1 d1 ?& mu r (d1, d2) ?& mu x2 d2
