module InductiveSpec where

import Test.Hspec
import Inductive.Parse.ParseTypes
import Inductive.Syntax.Types
-- import Data.Either (isLeft)

shouldJustBe :: (HasCallStack, Show a, Eq a) => Maybe a -> a -> Expectation
shouldJustBe x y = shouldBe x (Just y)

nat :: Type
nat = TypeName "Nat"

string :: Type
string = TypeName "String"

dog :: Type
dog = TypeName "Dog"



spec :: Spec
spec =
    describe "Inductive.parseType" $ do
        it "can parse type names" $
            parseType "Nat" `shouldJustBe` nat
        it "can parse product types (2)" $
            parseType "Nat * String" `shouldJustBe` (ProdType [nat, string])
        it "can parse product types (3)" $
            parseType "Nat * String * Dog" `shouldJustBe` (ProdType [nat, string, dog])
        it "can parse product types (weird whitespace)" $
            parseType "Nat * String *Dog* String*Dog" `shouldJustBe` (ProdType [nat, string, dog, string, dog])
        it "can parse function types (2)" $
            parseType "Nat -> String" `shouldJustBe` (FnType nat string)
        it "can parse function types (3)" $
            parseType "Nat -> String -> Dog" `shouldJustBe` (FnType nat (FnType string dog))
        it "can parse function types (weird whitespace)" $
            parseType "Nat -> String ->Dog-> String->Dog" `shouldJustBe` (FnType nat $ FnType string $ FnType dog $ FnType string dog)
        it "can parse function types (grouping)" $
            parseType "(Nat -> String) -> Nat -> Dog" `shouldJustBe` (FnType (FnType nat string) (FnType nat dog))