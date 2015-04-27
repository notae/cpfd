{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module FuzzySpec where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck       hiding ((.&.))

import           Control.Applicative ((<$>))
import           Data.Foldable       (Foldable)
import qualified Data.Foldable       as Foldable

import Data.Fuzzy

spec :: Spec
spec = do
  gradeSpec
  fsetSpec

instance Arbitrary DGrade where
  -- TBD: ranged values
--   arbitrary = fromRational <$> arbitrary
  arbitrary = elements [minBound, 0.3, 0.5, 0.8, maxBound]

instance Arbitrary RGrade where
  -- TBD: ranged values
  arbitrary = elements [minBound, 0.3, 0.5, 0.8, maxBound]

gradeSpec :: Spec
gradeSpec = do
  describe "DGrade" $ do
    prop "and-assoc"
      (fuzzyAndAssocProp :: DGrade -> DGrade -> DGrade -> Bool)
    prop "or-assoc"
      (fuzzyOrAssocProp :: DGrade -> DGrade -> DGrade -> Bool)
    -- TBD: not hold as DGrade is based on inexact Double
    -- prop "not-not"
    --   (fuzzyNotProp :: DGrade -> Bool)

  describe "RGrade" $ do
    prop "and-assoc"
      (fuzzyAndAssocProp :: RGrade -> RGrade -> RGrade -> Bool)
    prop "or-assoc"
      (fuzzyOrAssocProp :: RGrade -> RGrade -> RGrade -> Bool)
    prop "and-left-id"
      (fuzzyAndLeftIdProp :: RGrade -> Bool)
    prop "and-right-id"
      (fuzzyAndRightIdProp :: RGrade -> Bool)
    prop "or-left-id"
      (fuzzyOrLeftIdProp :: RGrade -> Bool)
    prop "or-right-id"
      (fuzzyOrRightIdProp :: RGrade -> Bool)
    prop "not-not"
      (fuzzyNotProp :: RGrade -> Bool)
    prop "fand-null"
      (gradeAndNullProp ([] :: [RGrade]) :: Bool)
    prop "for-null"
      (gradeOrNullProp ([] :: [RGrade]) :: Bool)

type MFS = Map Int RGrade
type FS = Membership Int RGrade
-- type MFS = MapFSet Int RGrade
-- type MFFS = MFFSet' Int RGrade

instance Arbitrary MFS where
  arbitrary = fromList <$> arbitrary

-- instance Arbitrary MFFS where
--   arbitrary = mfFSet' <$> arbitrary

fsetSpec :: Spec
fsetSpec = do
  describe "Map" $ do
    prop "and-assoc"
      (fuzzyAndAssocProp :: MFS -> MFS -> MFS -> Bool)
    prop "or-assoc"
      (fuzzyOrAssocProp :: MFS -> MFS -> MFS -> Bool)
    -- TBD: not implemented
    -- prop "not-not"
    --   (fuzzyNotProp :: MFS -> Bool)
    prop "$? id"
      (fsetIdProp :: MFS -> Int -> Bool)
    prop "$? comp"
      (fsetCompProp :: MFS -> (Int -> Int) -> (Int -> Int) -> Int -> Bool)
  describe "Membership (->)" $ do
    return ()
    -- TBD: function quality
    -- prop "and-assoc"
    --   (fuzzyAndAssocProp :: MFFS -> MFFS -> MFFS -> Bool)
    -- prop "or-assoc"
    --   (fuzzyOrAssocProp :: MFFS -> MFFS -> MFFS -> Bool)
    -- TBD: not implemented
    -- prop "not-not"
    --   (fuzzyNotProp :: MFS -> Bool)
    -- prop "$? id"
    --   (fsetIdProp :: FS -> Int -> Bool)
    -- prop "$? comp"
    --   (fsetCompProp :: FS -> (Int -> Int) -> (Int -> Int) -> Int -> Bool)

fsetIdProp :: (Fuzzy (s a g), FSetApply s, Ord a, Grade g) =>
              (s a g) -> a -> Bool
fsetIdProp s x = mu (id ?$ s) x == mu s x

fsetCompProp :: (Fuzzy (s a g), FSetApply s, Ord a, Grade g) =>
                (s a g) -> (a -> a) -> (a -> a) -> a -> Bool
fsetCompProp s f g x = mu ((g . f) ?$ s) x == mu (g ?$ f ?$ s) x

-- Typeclass Laws

fuzzyAndAssocProp :: (Fuzzy a, Eq a) => a -> a -> a -> Bool
fuzzyAndAssocProp x y z = ((x ?& y) ?& z) == (x ?& (y ?& z))

fuzzyOrAssocProp :: (Fuzzy a, Eq a) => a -> a -> a -> Bool
fuzzyOrAssocProp x y z = ((x ?| y) ?| z) == (x ?| (y ?| z))

fuzzyNotProp :: (Fuzzy a, Eq a) => a -> Bool
fuzzyNotProp x = x == fnot (fnot x)

fuzzyAndLeftIdProp :: Grade g => g -> Bool
fuzzyAndLeftIdProp x = x == (maxBound ?& x)

fuzzyAndRightIdProp :: Grade g => g -> Bool
fuzzyAndRightIdProp x = x == (x ?& maxBound)

fuzzyOrLeftIdProp :: Grade g => g -> Bool
fuzzyOrLeftIdProp x = x == (minBound ?| x)

fuzzyOrRightIdProp :: Grade g => g -> Bool
fuzzyOrRightIdProp x = x == (x ?| minBound)

gradeAndNullProp :: (Foldable f, Grade g) => f g -> Bool
gradeAndNullProp f = length (Foldable.toList f) == 0 && fand f == maxBound

gradeOrNullProp :: (Foldable f, Grade g) => f g -> Bool
gradeOrNullProp f = length (Foldable.toList f) == 0 && for f == minBound
