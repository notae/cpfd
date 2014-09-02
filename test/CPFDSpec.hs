module CPFDSpec where

import Control.CPFD
import Test.Hspec
-- import Test.Hspec.QuickCheck (prop)
-- import Test.QuickCheck hiding ((.&.))


spec :: Spec
spec = do

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
