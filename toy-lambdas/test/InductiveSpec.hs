module InductiveSpec where

import Test.Hspec
import Inductive.Parse.ParseTypes
import Inductive.Syntax.Types
-- import Data.Either (isLeft)

shouldJustBe :: (HasCallStack, Show a, Eq a) => Maybe a -> a -> Expectation
shouldJustBe x y = shouldBe x (Just y)

spec :: Spec
spec =
    describe "Inductive.parseType" $
        it "can parse type names" $
            parseType "Nat" `shouldJustBe` TypeName "Nat"