module InductiveSpec where

import Test.Hspec
import Inductive.Parse.ParseTypes
import Inductive.Parse.ParseExpr
import Inductive.Syntax.Types
import Inductive.Syntax.Expr
-- import Data.Either (isLeft)

shouldJustBe :: (HasCallStack, Show a, Eq a) => Maybe a -> a -> Expectation
shouldJustBe x y = shouldBe x (Just y)

nat :: Type
nat = TypeName "Nat"

string :: Type
string = TypeName "String"

dog :: Type
dog = TypeName "Dog"

x :: Expr
x = ExprVar "x"

y :: Expr
y = ExprVar "y"

zebra :: Expr
zebra = ExprVar "zebra"

spec :: Spec
spec = do
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
    
    describe "Inductive.parseExpr" $ do
        it "can parse variable names" $
            parseExpr "x" `shouldJustBe` x
        it "can parse int literals" $
            parseExpr "3732" `shouldJustBe` (ExprLit $ LitInt 3732)
        it "can parse bool literal false" $
            parseExpr "false" `shouldJustBe` (ExprLit $ LitBool False)
        it "can parse bool literal true" $
            parseExpr "true" `shouldJustBe` (ExprLit $ LitBool True)
        it "can parse let expressions" $
            parseExpr "let x = y in zebra" `shouldJustBe` (ExprLet "x" y zebra)
        it "can parse nested let expressions" $
            parseExpr "let x = 56 in let y = zebra in 123" `shouldJustBe` (ExprLet "x" (ExprLit $ LitInt 56) (ExprLet "y" zebra (ExprLit $ LitInt 123)))
        it "can parse ITE" $
            parseExpr "if y then 53 else zebra" `shouldJustBe` (ExprITE y (ExprLit $ LitInt 53) zebra)
        it "can parse app (2)" $
            parseExpr "x y" `shouldJustBe` (ExprApp x y)
        it "can parse app (3)" $
            parseExpr "x zebra y" `shouldJustBe` (ExprApp (ExprApp x zebra) y)
        it "can parse app (left parens)" $
            parseExpr "(x zebra) y" `shouldJustBe` (ExprApp (ExprApp x zebra) y)
        it "can parse app (right parens)" $
            parseExpr "x (zebra y)" `shouldJustBe` (ExprApp x (ExprApp zebra y))
        it "can parse app (outer parens)" $
            parseExpr "(x zebra y)" `shouldJustBe` (ExprApp (ExprApp x zebra) y)
        it "can parse app in let exprs" $
            parseExpr "let x = zebra y in zebra x" `shouldJustBe` (ExprLet "x" (ExprApp zebra y) (ExprApp zebra x))
        it "can parse app in let exprs (parens)" $
            parseExpr "(let x = zebra y in zebra) x" `shouldJustBe` (ExprApp (ExprLet "x" (ExprApp zebra y) zebra) x)
        it "can parse app in ITE" $
            parseExpr "if zebra y then y x else zebra x" `shouldJustBe` ExprITE (ExprApp zebra y) (ExprApp y x) (ExprApp zebra x)
        it "can parse app in ITE (parens)" $
            parseExpr "(if zebra y then y x else zebra) x" `shouldJustBe` ExprApp (ExprITE (ExprApp zebra y) (ExprApp y x) zebra) x