{-# LANGUAGE TypeSynonymInstances #-}

module CPFDSpec where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck hiding ((.&.))

import Control.CPFD
import qualified Control.CPFD.Domain as Domain
import Control.Applicative ((<$>), (<*>))
import Data.List (nub, sort)

instance (Arbitrary a, Ord a) => Arbitrary (Domain a) where
  arbitrary = Domain.fromList <$> arbitrary

spec :: Spec
spec = do

  describe "Domain" $ do
    prop "fromList/toList round-trip" $ \xs ->
      Domain.toList (Domain.fromList (sort (nub xs))) == sort (nub (xs :: [Int]))

  describe "CTraversabe#cup" $ do
    let c = [123::Int, 456]
    let cList  = CTraversable [[123::Int], [456]]
    it "to []" $ cup (:[]) c `shouldBe` cList

  describe "CTraversable#cdown" $ do
    let c = [123::Int, 456]
    let cList  = CTraversable [[123::Int], [456]]
    it "from []" $ cdown head cList `shouldBe` c

  describe "runFD" $ do
    it "empty monad" $
      (runFD $ return ()) `shouldBe` ()

  describe "labelT" $ do
    it "empty label" $
      (runFD $ labelT []) `shouldBe` ([[]] :: [[Int]])
    prop "single label" $ \d ->
      runFD (new d >>= \v -> labelT [v]) == map (:[]) (Domain.toList (d :: Domain Int))

  describe "eq" $ do
    prop "reflexive" $ \d ->
      runFD (do {v <- new d; v `eq` v; get v}) == (d :: Domain Int)

  describe "add3" $ do
    prop "monotonic" prop_constraint_add3

prop_constraint_add3 :: (Domain Int, Domain Int, Domain Int) -> Bool
prop_constraint_add3 (x, y, z) =
  x' `Domain.isSubsetOf` x
  &&
  y' `Domain.isSubsetOf` y
  &&
  z' `Domain.isSubsetOf` z
  where
    (x', y', z') = runFD $ do
      vx <- new x
      vy <- new y
      vz <- new z
      add3 vz vx vy
      (,,) <$> get vx <*> get vy <*> get vz
