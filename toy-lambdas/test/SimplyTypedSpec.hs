module SimplyTypedSpec where

import Test.Hspec
import SimplyTyped

c1 = [Decl "a" (TVar "A"), Decl "b" (TVar "B")]
c2 = [Decl "a" (TVar "A"), Decl "a" (TVar "B")]
c3 = [Decl "a" (TVar "A"), Decl "b" (TVar "B"), Decl "c" (TVar "C"), Decl "d" (TVar "D"),
      Decl "e" (TVar "E"), Decl "f" (TVar "F"), Decl "g" (TVar "G"), Decl "a" (TVar "A")]
c4 = [Decl "a" (TVar "A"), Decl "b" (TVar "B"), Decl "c" (TVar "C"), Decl "d" (TVar "D"),
      Decl "e" (TVar "E"), Decl "f" (TVar "F"), Decl "g" (TVar "G"), Decl "h" (TVar "H")]

tpA = TVar "A"
tpB = TVar "B"
tpC = TVar "C"
tpD = TVar "D"
tpE = TVar "E"

tpA_B = TArrow (TVar "A") (TVar "B")
tpB_C = TArrow (TVar "B") (TVar "C")
tpC_D = TArrow (TVar "C") (TVar "D")
tpA__B_C = TArrow (TVar "A") $ TArrow (TVar "B") (TVar "C")
tpA_B__C = TArrow (TArrow (TVar "A") (TVar "B")) (TVar "C")
tpA_B__C_D___E = TArrow (TArrow tpA_B tpC_D) tpE
tpA_B_C_D_E = TArrow tpA (TArrow tpB (TArrow tpC (TArrow tpD tpE)))
tpA_B__C___D_E = TArrow (TArrow (TArrow tpA tpB) tpC) (TArrow tpD tpE)


spec :: Spec
spec = do
    describe "SimplyTyped.context" $ do
        it ((show c1) ++ " is a well-formed context") $ do
            (checkContextInvariant c1) `shouldBe` True
        it ((show c2) ++ " has repeated domain \"a\"") $ do
            (checkContextInvariant c2) `shouldBe` False
        it ((show c3) ++ " has repeated domain \"a\"") $ do
            (checkContextInvariant c3) `shouldBe` False
        it ((show c4) ++ " is a well formed context") $ do
            (checkContextInvariant c4) `shouldBe` True

    describe "SimplyTyped.parseType" $ do
        it "Error parsing arrow type: `A -> B`" $ do
          (parseType "A -> B") `shouldBe` tpA_B
        it "Error parsing arrow type without spaces: `A->B`" $ do
          (parseType "A -> B") `shouldBe` tpA_B
        it "Parsing should handle arbitrary complexity: `(A->B) -> (C->D) -> E`" $ do
          (parseType "(A->B) -> (C->D) -> E") `shouldBe` tpA_B__C_D___E
        it "Arrow types are right associative: `A->B->C->D->E`" $ do
          (parseType "A->B->C->D->E") `shouldBe` tpA_B_C_D_E
        it"Nested parentheses: `((A->B)->C)->D->E`" $ do
          (parseType "A->B->C->D->E") `shouldBe` tpA_B__C___D_E

