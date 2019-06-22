module DependentlyTyped.ParseSpec where

import Test.Hspec
import DependentlyTyped.Syntax
import DependentlyTyped.Parse


x = Var "x"
y = Var "y"
z = Var "z"
a = Var "a"
b = Var "b"
c = Var "c"
d = Var "d"
id_ = Lambda (Decl "A" (SType S)) (Lambda (Decl "x" (TConstr (TVar "A"))) x)
fid_ = Lambda (Decl "A" (SType (SArrow S S))) (Lambda (Decl "x" (TConstr (TVar "A"))) x)
polyAppl = Appl fid_ (TTerm (TConstr (TArrow (TVar "B") (TVar "C"))))
id_id = Appl id_ id_


spec :: Spec
spec = do
    describe "DependentlyTyped.parseType" $ do
      it "parsing a TVar" $ do
        (parseType "A") `shouldBe` (TConstr (TVar "A"))
      it "parsing a super type" $ do
        (parseType "*") `shouldBe` (SType S)
      it "parsing a complicated super type" $ do
        (parseType "(* -> *) -> * -> *") `shouldBe` (SType (SArrow (SArrow S S) (SArrow S S)))
    describe "DependentlyTyped.parse" $ do
      it "parsing a variable" $ do
        (parse "x") `shouldBe` x
      it "parsing appl" $ do
        (parse "f x") `shouldBe` (Appl (Var "f") (Var "x"))
      it "parsing id" $ do
        (parse "λ x : A . x") `shouldBe` (Lambda (Decl "x" (TConstr (TVar "A"))) x)
      it "parsing polymorphic id" $ do
        (parse "λ A : * . \\ x : A . x") `shouldBe` id_
      it "parsing type appl" $ do
        (parse "(\\ A : * -> * . \\ x : A . x) (B -> C)") `shouldBe` polyAppl
