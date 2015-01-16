-- | Fuzzy Constraint Satisfaction Problem Solver

{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Control.CPFD.Fuzzy
       (
         FS, FR, FR1, FR2, FR3
       , FC (..)
       , cons
       ) where

import Data.List   (foldl')
import Debug.Trace (traceShow)

import Data.Fuzzy

-- Types

type FS a g = Map a g
type FR a g = Membership (a, a) g
type FR1 a g = Membership a g
type FR2 a b g = Membership (a, b) g
type FR3 a b c g = Membership (a, b, c) g

data FC g = forall s a. (FSet s, Show (s a g)) => FC (s a g)
deriving instance Show (FC g)

data FCSP g =
  FCSP
  { cs :: FC g
  } deriving (Show)

data Assign

-- FCSP Solver

-- solve ::

eval :: Grade g => FCSP g -> Assign -> g
eval = undefined

revise :: (Fuzzy (r (a, b) g), FSet r,
           Fuzzy (s a g), Fuzzy (s b g), FSet s, FSetUpdate s,
           FValue a, FValue b, Grade g) =>
           r (a, b) g -> s a g -> s b g -> g -> (g, Bool, s a g)
revise r x1 x2 sup = (sup', changed, x1') where
  sup' = sup ?& height
  (changed, height, x1') = foldArc (revise0 r x2) (False, minBound, x1) x1 x2

revise0 :: (Fuzzy (r (a, b) g), FSet r,
            Fuzzy (s a g), Fuzzy (s b g), FSet s, FSetUpdate s,
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

foldArc :: (Fuzzy (s a g), FSet s, Ord a, Ord b, Grade g) =>
           (c -> (a, b) -> c) -> c -> s a g -> s b g -> c
foldArc f c x1 x2 = foldl' g c (support x1) where
  g c' d1 = foldl' (\c'' d2 -> f c'' (d1, d2)) c' (support x2)

cons :: (Fuzzy (r (a, b) g), FSet r,
         Fuzzy (s a g), Fuzzy (s b g), FSet s,
         Ord a, Ord b, Grade g) =>
        r (a, b) g -> s a g -> s b g -> a -> b -> g
cons r x1 x2 d1 d2 = mu x1 d1 ?& mu r (d1, d2) ?& mu x2 d2
