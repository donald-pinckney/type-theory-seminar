module SimplyTypedSpec where

import Test.Hspec
import SimplyTyped.SimplyTyped
import SimplyTyped.Parse
import Data.Either (isLeft)

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
tpA_B__C_D___E = TArrow tpA_B (TArrow tpC_D tpE)
tpA_B_C_D_E = TArrow tpA (TArrow tpB (TArrow tpC (TArrow tpD tpE)))
tpA_B__C___D_E = TArrow (TArrow (TArrow tpA tpB) tpC) (TArrow tpD tpE)

zero = (parse "λ f : A -> A . λ x : A . x")
one = (parse "λ f : A -> A . λ x : A . f x")
two = (parse "λ f : A -> A . λ x : A . f (f x)")
add = (parse "λ m : (A -> A) -> A -> A . λ n : (A -> A) -> A -> A . λ f : A -> A . λ x : A . m f (n f x)")
mult = (parse "λ m : (A -> A) -> A -> A . λ n : (A -> A) -> A -> A . λ f : A -> A . λ x : A . m (n f) x")

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
        it "Parsing should handle arbitrary complexity: `(A->B) -> C -> D`" $ do
          (parseType "(A->B) -> C -> D") `shouldBe` TArrow (TArrow (TVar "A") (TVar "B")) (TArrow (TVar "C") (TVar "D"))
        it "Parsing should handle arbitrary complexity: `(A->B) -> (C->D) -> E`" $ do
          (parseType "(A->B) -> (C->D) -> E") `shouldBe` tpA_B__C_D___E
        it "Arrow types are right associative: `A->B->C->D->E`" $ do
          (parseType "A->B->C->D->E") `shouldBe` tpA_B_C_D_E
        it"Nested parentheses: `((A->B)->C)->D->E`" $ do
          (parseType "((A->B)->C)->D->E") `shouldBe` tpA_B__C___D_E

    describe "SimplyTyped.typecheck" $ do
        it "Checking var when present in context" $ do
          (check c1 (Var "a")) `shouldBe` Right (TVar "A")

        it "Checking var when not present in context" $ do
          isLeft (check c1 (Var "z")) `shouldBe` True

        it "Checking identity function with bound var not in context" $ do
          (check [] (Lambda (Decl "a" (TVar "A")) (Var "a")))
          `shouldBe`
          Right (TArrow (TVar "A") (TVar "A"))

        it "Checking function with free var in context" $ do
          (check [(Decl "b" (TVar "B"))] (Lambda (Decl "a" (TVar "A")) (Var "b")))
          `shouldBe`
          Right (TArrow  (TVar "A") (TVar "B"))

        it "Checking function with free var not in context" $ do
          isLeft (check [] (Lambda (Decl "a" (TVar "A")) (Var "b")))
          `shouldBe`
          True

        it "Checking function with bound var in context" $ do
          (check c4 (Lambda (Decl "a" (TVar "X")) (Var "b")))
          `shouldBe`
          Right (TArrow (TVar "X") (TVar "B"))

        it "Checking nested abstraction" $ do
          (check [] (Lambda (Decl "a" (TVar "A")) (Lambda (Decl "b" (TVar "B")) (Var "a"))))
          `shouldBe`
          Right (TArrow (TVar "A") (TArrow (TVar "B") (TVar "A")))

        it "Checking nested abstraction with shadowed bound variable" $ do
          (check c4 (Lambda (Decl "a" (TVar "B")) (Lambda (Decl "a" (TVar "C")) (Var "a"))))
          `shouldBe`
          Right (TArrow (TVar "B") (TArrow (TVar "C") (TVar "C")))

        it "Checking application of non arrow type" $ do
          isLeft (check [(Decl "a" (TVar "B"))] (Appl (Var "a") (Var "b")))
          `shouldBe`
          True

        it "Checking application of arrow type with correct domain type" $ do
          (check [ Decl "a" (TArrow (TVar "A") (TVar "B"))
                 , Decl "b" (TVar "A")
                 ]
                 (Appl (Var "a") (Var "b")))
          `shouldBe`
          Right (TVar "B")

        it "Checking application of arrow type with incorrect domain type" $ do
          isLeft (check [ Decl "a" (TArrow (TVar "A") (TVar "B"))
                 , Decl "b" (TVar "B")
                 ]
                 (Appl (Var "a") (Var "b")))
          `shouldBe`
          True

        it "Checking complicated expression" $ do
          -- a : A
          -- b : B
          -- f : A -> B -> C
          -- ((\\a : A . \\b : B . \\f : A -> B -> C . (f a) b) x) y
          check [Decl "x" (TVar "A"), Decl "y" (TVar "B")] 
                (Appl (Appl (Lambda (Decl "a" (TVar "A"))
                      (Lambda (Decl "b" (TVar "B"))
                        (Lambda (Decl "f" (TArrow (TVar "A") (TArrow (TVar "B") (TVar "C"))))
                          (Appl (Appl (Var "f") (Var "a")) (Var "b"))))) (Var "x")) (Var "y"))
          `shouldBe`
          Right (TArrow (TArrow (TVar "A") (TArrow (TVar "B") (TVar "C"))) (TVar "C"))

    describe "SimplyTyped.substitute" $ do
        it "Lambda" $ do
          (substitute "x" (Var "y") (Lambda (Decl "z" (TVar "A")) (Var "x")))
          `shouldBe`
          (Lambda (Decl "z" (TVar "A")) (Var "y"))

        it "Lambda scope overwrite" $ do
          (substitute "x" (Var "y") (Lambda (Decl "x" (TVar "A")) (Var "x")))
          `shouldBe`
          (Lambda (Decl "x" (TVar "A")) (Var "x"))

    describe "SimplyTyped.exec" $ do
        it "(\\x . x) y ->_\\beta y" $ do
          (exec (parse "(λ x : A . x) y"))
          `shouldBe`
          (Var "y")
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
