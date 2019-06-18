module UntypedSpec where

import Test.Hspec
import Untyped.Semantics
import Untyped.Parse


x = Var "x"
y = Var "y"
z = Var "z"
a = Var "a"
b = Var "b"
c = Var "c"
d = Var "d"
id_ = Abst "x" x
id_id = Appl id_ id_
idy = Abst "y" y

zero = parse "λ f . λ x . x"
one = parse "λ f . λ x . (f x)"
two = parse "λ f . λ x . f (f x)"
add = parse "λ m . λ n . λ f . λ x . m f (n f x)"
mult = parse "λ m . λ n . λ f . λ x . m (n f) x"

add_term = Abst "m" (Abst "n" (Abst "f" (Abst "x" (
               Appl (Appl (Var "m") (Var "f")) (Appl (Appl (Var "n") (Var "f")) (Var "x"))
           ))))

spec :: Spec
spec = do
    describe "Untyped.parse" $ do
        it "parsing a variable" $ do
            (parse "x") `shouldBe` x
        it "parsing a variable" $ do
            (parse "y") `shouldBe` y
        it "parsing an application" $ do
            (parse "x y") `shouldBe` (Appl x y)
        it "application should be left associative" $ do
            (parse "x x x") `shouldBe` (Appl (Appl x x) x)
        it "application should be left associative" $ do
            (parse "a b c d") `shouldBe` (Appl (Appl (Appl a b) c) d)
        it "abstraction should bind looser than application" $ do
            (parse "\\ x . x x x ") `shouldBe` (Abst "x" (Appl (Appl x x) x))
        it "parsing add" $ do
            add `shouldBe` add_term

    describe "Untyped.normal" $ do
        it "Vars are in normal form" $ do
            (normal x) `shouldBe` True
        it "Application of two vars is normal" $ do
            (normal $ Appl x y) `shouldBe` True
        it "Application of abstraction is not normal" $ do
            (normal $ Appl id_ y) `shouldBe` False
        it "Application of abstraction is not normal" $ do
            (normal $ id_id) `shouldBe` False
        it "Application of abstraction is not normal" $ do
            (normal $ Appl x id_) `shouldBe` True
        it "Application with non-normal rhs is not normal" $ do
            (normal $ Appl x id_id) `shouldBe` False
        it "Application with non-normal lhs is not normal" $ do
            (normal $ Appl id_id x) `shouldBe` False

    describe "Untyped.betaReduce" $ do
        it "`(λ x . x) x` should reduce to x" $ do
            (betaReduce (Appl id_ x)) `shouldBe` x
        it "`(λ x . x) ((λ x . x) (λ x . x))` should reduce to `(λ x . x) (λ x . x)`" $ do
            (betaReduce (Appl id_ id_id)) `shouldBe` id_id
        it  "`(λ y . y) ((λ x . x) (λ x . x))` should reduce to `(λ x . x) (λ x . x)`" $ do
            (betaReduce (Appl idy id_id)) `shouldBe` id_id
        it "`λ x . (λ x . x) x`  should reduce to `λ x . x`" $ do
            (betaReduce (Appl x (Appl id_ x))) `shouldBe` (Appl x x)

    describe "Untyped.exec" $ do
        it "one + one = two" $ do
            (exec (Appl (Appl add one) one))
            `shouldBe`
            two
        it "two * two = two + two" $ do
            (exec (Appl (Appl mult two) two))
            `shouldBe`
            (exec (Appl (Appl add two) two))
        it "two * zero = zero" $ do
            (exec (Appl (Appl mult two) zero))
            `shouldBe`
            zero
