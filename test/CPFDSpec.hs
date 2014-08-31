module CPFDSpec where

import Control.CPFD
import Data.Maybe (maybeToList)
import Test.Hspec
-- import Test.Hspec.QuickCheck (prop)
-- import Test.QuickCheck hiding ((.&.))


spec :: Spec
spec = do

  describe "List#cmap" $ do
    let cMaybe = CList [Just (123::Int), Nothing]
    let cList  = CList [[123], []]
    it "id" $
      cmap id cMaybe `shouldBe` cMaybe
    it "maybeToList" $
      cmap maybeToList cMaybe `shouldBe` cList

  describe "runFD" $ do
    it "empty monad" $
      (runFD $ return ()) `shouldBe` ()
