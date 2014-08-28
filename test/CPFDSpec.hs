module CPFDSpec where

import Control.CPFD
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck hiding ((.&.))
import Data.Maybe (maybeToList)


spec :: Spec
spec = do

  describe "List#cmap" $ do
    let cMaybe = List [Just 123, Nothing]
    let cList  = List [[123], []]
    it "id" $
      cmap id cMaybe `shouldBe` cMaybe
    it "maybeToList" $
      cmap maybeToList cMaybe `shouldBe` cList

  describe "runFD" $ do
    it "empty monad" $
      (runFD $ return ()) `shouldBe` ()
