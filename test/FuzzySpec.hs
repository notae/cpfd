{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module FuzzySpec where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck       hiding ((.&.))

import Control.Applicative ((<$>))
import Data.Fuzzy

spec :: Spec
spec = do
  gradeSpec
  fsetSpec

instance Arbitrary DGrade where
--   arbitrary = fromRational <$> arbitrary
  arbitrary = elements [minBound, 0.3, 0.5, 0.8, maxBound]

instance Arbitrary RGrade where
  arbitrary = elements [minBound, 0.3, 0.5, 0.8, maxBound]

gradeSpec :: Spec
gradeSpec = do
  describe "DGrade" $ do
    prop "and-assoc"
      (fuzzyAndAssocProp :: DGrade -> DGrade -> DGrade -> Bool)
    prop "or-assoc"
      (fuzzyOrAssocProp :: DGrade -> DGrade -> DGrade -> Bool)
    -- TBD: not hold as DGrade is based on inexact Double
    -- prop "inv"
    --   (fuzzyInvProp :: DGrade -> Bool)

  describe "RGrade" $ do
    prop "and-assoc"
      (fuzzyAndAssocProp :: RGrade -> RGrade -> RGrade -> Bool)
    prop "or-assoc"
      (fuzzyOrAssocProp :: RGrade -> RGrade -> RGrade -> Bool)
    prop "inv"
      (fuzzyInvProp :: RGrade -> Bool)
--     prop "and-left-id"
--       (gradeAndLeftIdProp :: RGrade -> Bool)
--     prop "and-right-id"
--       (gradeAndRightIdProp :: RGrade -> Bool)

type MFS = MapFuzzySet Int RGrade

instance Arbitrary MFS where
  arbitrary = fromList <$> arbitrary

fsetSpec :: Spec
fsetSpec = do
  describe "MapFuzzySet" $ do
    prop "and-assoc"
      (fuzzyAndAssocProp :: MFS -> MFS -> MFS -> Bool)
    prop "or-assoc"
      (fuzzyOrAssocProp :: MFS -> MFS -> MFS -> Bool)
    -- TBD: not implemented
    -- prop "inv"
    --   (fuzzyInvProp :: MFS -> Bool)

-- Laws

fuzzyAndAssocProp :: (Fuzzy a, Eq a) => a -> a -> a -> Bool
fuzzyAndAssocProp x y z = ((x ?& y) ?& z) == (x ?& (y ?& z))

fuzzyOrAssocProp :: (Fuzzy a, Eq a) => a -> a -> a -> Bool
fuzzyOrAssocProp x y z = ((x ?| y) ?| z) == (x ?| (y ?| z))

fuzzyInvProp :: (Fuzzy a, Eq a) => a -> Bool
fuzzyInvProp x = x == inv (inv x)

gradeAndLeftIdProp :: Grade g => g -> Bool
gradeAndLeftIdProp x = x == (maxBound ?& x)

gradeAndRightIdProp :: Grade g => g -> Bool
gradeAndRightIdProp x = x == (x ?& maxBound)
