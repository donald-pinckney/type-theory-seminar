module defs.AlphaEquivalence

import defs.Identifier
import defs.BindingDepth
import Data.Fin
import Data.So
import Decidable.Order
import defs.AST

%default total

data AllEquiv : (p : t -> t -> Type) -> List t -> List t -> Type where
    ConsEquiv : p h1 h2 -> AllEquiv p rest1 rest2 -> AllEquiv p (h1 :: rest1) (h2 :: rest2)
    NilEquiv : AllEquiv p [] []

implementation Preorder t p => Preorder (List t) (AllEquiv p) where
    reflexive [] = NilEquiv
    reflexive (x :: xs) = ConsEquiv (reflexive x) (reflexive xs)

    transitive (h1 :: rest1) (h2 :: rest2) (h3 :: rest3) (ConsEquiv h1h2 rest1rest2) (ConsEquiv h2h3 rest2rest3) = ConsEquiv (transitive h1 h2 h3 h1h2 h2h3) (transitive rest1 rest2 rest3 rest1rest2 rest2rest3)
    transitive [] [] [] NilEquiv NilEquiv = NilEquiv

implementation Equivalence t p => Equivalence (List t) (AllEquiv p) where
    symmetric (h1 :: rest1) (h2 :: rest2) (ConsEquiv h1h2 rest1rest2) = ConsEquiv (symmetric h1 h2 h1h2) (symmetric rest1 rest2 rest1rest2)
    symmetric [] [] NilEquiv = NilEquiv


isAllEquiv : (xs : List t) -> (ys : List t) -> ((x : t) -> (y : t) -> Dec (p x y)) -> Dec (AllEquiv p xs ys)
isAllEquiv [] [] isEquiv = Yes NilEquiv
isAllEquiv (x :: xs) (y :: ys) isEquiv = case (isEquiv x y, isAllEquiv xs ys isEquiv) of
    (Yes xy, Yes xsys) => Yes (ConsEquiv xy xsys)
    (No xy_c, Yes xsys) => No (\sup => case sup of
        (ConsEquiv xy xsys') => xy_c xy
    )
    (Yes xy, No xsys_c) => No (\sup => case sup of
        (ConsEquiv xy' xsys) => xsys_c xsys
    )
    (No xy_c, No xsys_c) => No (\sup => case sup of
        (ConsEquiv xy xsys') => xy_c xy
    )
isAllEquiv (x :: xs) [] isEquiv = No (\sup => case sup of
    (ConsEquiv _ _) impossible
    NilEquiv impossible
)
isAllEquiv [] (y :: ys) isEquiv = No (\sup => case sup of
    (ConsEquiv _ _) impossible
    NilEquiv impossible
)

data AlphaEquivalent : AExpr d -> AExpr d -> Type where
    AlphaEquivalentPostulate : AlphaEquivalent AExprPostulate AExprPostulate
    AlphaEquivalentStar : AlphaEquivalent AExprStar AExprStar
    AlphaEquivalentBox : AlphaEquivalent AExprBox AExprBox
    AlphaEquivalentVariable : AlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x src1)) (AExprVariable (MkDeBruijnIdentifier x src2))
    AlphaEquivalentLambda : AlphaEquivalent t1 t2 -> AlphaEquivalent m1 m2 -> AlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2)
    AlphaEquivalentArrow : AlphaEquivalent t1 t2 -> AlphaEquivalent m1 m2 -> AlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2)
    AlphaEquivalentDefApp : AllEquiv AlphaEquivalent args1 args2 -> AlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x src1) args1) (AExprDefApp (MkDeBruijnIdentifier x src2) args2)
    AlphaEquivalentApp : AlphaEquivalent l1 l2 -> AlphaEquivalent r1 r2 -> AlphaEquivalent (AExprApp l1 r1) (AExprApp l2 r2)

implementation Preorder (AExpr d) AlphaEquivalent where
    reflexive AExprPostulate = AlphaEquivalentPostulate
    reflexive (AExprLambda (MkADecl t src) m) = AlphaEquivalentLambda (reflexive t) (reflexive m)
    reflexive (AExprVariable (MkDeBruijnIdentifier x src)) = AlphaEquivalentVariable
    reflexive (AExprApp x y) = AlphaEquivalentApp (reflexive x) (reflexive y)
    reflexive (AExprDefApp (MkDeBruijnIdentifier x src) args) = AlphaEquivalentDefApp (reflexive args)
    reflexive AExprStar = AlphaEquivalentStar
    reflexive AExprBox = AlphaEquivalentBox
    reflexive (AExprArrow (MkADecl t src) m) = AlphaEquivalentArrow (reflexive t) (reflexive m)

    transitive AExprPostulate AExprPostulate AExprPostulate AlphaEquivalentPostulate AlphaEquivalentPostulate = AlphaEquivalentPostulate
    transitive AExprStar AExprStar AExprStar AlphaEquivalentStar AlphaEquivalentStar = AlphaEquivalentStar
    transitive AExprBox AExprBox AExprBox AlphaEquivalentBox AlphaEquivalentBox = AlphaEquivalentBox
    transitive (AExprVariable (MkDeBruijnIdentifier x src1)) (AExprVariable (MkDeBruijnIdentifier x src2)) (AExprVariable (MkDeBruijnIdentifier x src3)) AlphaEquivalentVariable AlphaEquivalentVariable = AlphaEquivalentVariable
    transitive (AExprApp l1 r1) (AExprApp l2 r2) (AExprApp l3 r3) (AlphaEquivalentApp l1l2 r1r2) (AlphaEquivalentApp l2l3 r2r3) = AlphaEquivalentApp (transitive l1 l2 l3 l1l2 l2l3) (transitive r1 r2 r3 r1r2 r2r3)
    transitive (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) (AExprLambda (MkADecl t3 src3) m3) (AlphaEquivalentLambda t1t2 m1m2) (AlphaEquivalentLambda t2t3 m2m3) = AlphaEquivalentLambda (transitive t1 t2 t3 t1t2 t2t3) (transitive m1 m2 m3 m1m2 m2m3)
    transitive (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) (AExprArrow (MkADecl t3 src3) m3) (AlphaEquivalentArrow t1t2 m1m2) (AlphaEquivalentArrow t2t3 m2m3) = AlphaEquivalentArrow (transitive t1 t2 t3 t1t2 t2t3) (transitive m1 m2 m3 m1m2 m2m3)
    transitive (AExprDefApp (MkDeBruijnIdentifier x src1) args1) (AExprDefApp (MkDeBruijnIdentifier x src2) args2) (AExprDefApp (MkDeBruijnIdentifier x src3) args3) (AlphaEquivalentDefApp args1args2) (AlphaEquivalentDefApp args2args3) = AlphaEquivalentDefApp (transitive args1 args2 args3 args1args2 args2args3)

implementation Equivalence (AExpr d) AlphaEquivalent where
    symmetric AExprPostulate AExprPostulate AlphaEquivalentPostulate = AlphaEquivalentPostulate
    symmetric AExprStar AExprStar AlphaEquivalentStar = AlphaEquivalentStar
    symmetric AExprBox AExprBox AlphaEquivalentBox = AlphaEquivalentBox
    symmetric (AExprVariable (MkDeBruijnIdentifier x src1)) (AExprVariable (MkDeBruijnIdentifier x src2)) AlphaEquivalentVariable = AlphaEquivalentVariable
    symmetric (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) (AlphaEquivalentLambda t1t2 m1m2) = AlphaEquivalentLambda (symmetric t1 t2 t1t2) (symmetric m1 m2 m1m2)
    symmetric (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) (AlphaEquivalentArrow t1t2 m1m2) = AlphaEquivalentArrow (symmetric t1 t2 t1t2) (symmetric m1 m2 m1m2)
    symmetric (AExprDefApp (MkDeBruijnIdentifier x src1) args1) (AExprDefApp (MkDeBruijnIdentifier x src2) args2) (AlphaEquivalentDefApp args1args2) = AlphaEquivalentDefApp (symmetric args1 args2 args1args2)
    symmetric (AExprApp l1 r1) (AExprApp l2 r2) (AlphaEquivalentApp l1l2 r1r2) = AlphaEquivalentApp (symmetric l1 l2 l1l2) (symmetric r1 r2 r1r2)


isAlphaEquivalent : (e1 : AExpr d) -> (e2 : AExpr d) -> Dec (AlphaEquivalent e1 e2)
isAlphaEquivalent AExprPostulate AExprPostulate = Yes AlphaEquivalentPostulate
isAlphaEquivalent AExprPostulate (AExprLambda x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprVariable x) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprApp x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprDefApp x xs) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate AExprStar = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate AExprBox = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprArrow x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )

isAlphaEquivalent AExprStar AExprStar = Yes AlphaEquivalentStar
isAlphaEquivalent AExprStar AExprPostulate = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprLambda x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprVariable x) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprApp x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprDefApp x xs) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar AExprBox = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprArrow x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )


isAlphaEquivalent AExprBox AExprBox = Yes AlphaEquivalentBox
isAlphaEquivalent AExprBox AExprPostulate = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprLambda x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprVariable x) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprApp x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprDefApp x xs) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox AExprStar = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprArrow x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )



isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprVariable (MkDeBruijnIdentifier x2 src2)) = case decEq x1 x2 of
    (Yes Refl) => Yes AlphaEquivalentVariable
    (No contra) => No (\sup => case sup of
        AlphaEquivalentVariable => contra Refl
    )

isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) AExprPostulate = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprLambda x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprApp x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprDefApp x xs) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) AExprStar = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) AExprBox = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprArrow x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )


isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) with (decEq x1 x2, isAllEquiv args1 args2 isAlphaEquivalent)
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (Yes x1x2, Yes args1args2) = rewrite x1x2 in Yes (AlphaEquivalentDefApp args1args2)
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (No x1x2_c, Yes args1args2) = No (\sup => case sup of
        (AlphaEquivalentDefApp args1args2') => x1x2_c Refl
    )
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (Yes x1x2, No args1args2_c) = No (\sup => case sup of
        (AlphaEquivalentDefApp args1args2) => args1args2_c args1args2
    )
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (No x1x2_c, No args1args2_c) = No (\sup => case sup of
        (AlphaEquivalentDefApp args1args2) => args1args2_c args1args2
    )

isAlphaEquivalent (AExprDefApp x args) AExprPostulate = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprLambda y z) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprVariable y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprApp y z) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) AExprStar = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) AExprBox = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprArrow y z) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )


isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) with (isAlphaEquivalent t1 t2, isAlphaEquivalent m1 m2)
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (Yes t1t2, Yes m1m2) = Yes (AlphaEquivalentLambda t1t2 m1m2)
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (No t1t2_c, Yes m1m2) = No (\sup => case sup of
        (AlphaEquivalentLambda t1t2 m1m2') => t1t2_c t1t2
    )
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (Yes t1t2, No m1m2_c) = No (\sup => case sup of
        (AlphaEquivalentLambda t1t2' m1m2) => m1m2_c m1m2
    )
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (No t1t2_c, No m1m2_c) = No (\sup => case sup of
        (AlphaEquivalentLambda t1t2' m1m2) => m1m2_c m1m2
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) AExprPostulate = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprArrow x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprVariable x) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprApp x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprDefApp x xs) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) AExprStar = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) AExprBox = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )


isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) with (isAlphaEquivalent t1 t2, isAlphaEquivalent m1 m2)
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (Yes t1t2, Yes m1m2) = Yes (AlphaEquivalentArrow t1t2 m1m2)
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (No t1t2_c, Yes m1m2) = No (\sup => case sup of
        (AlphaEquivalentArrow t1t2 m1m2') => t1t2_c t1t2
    )
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (Yes t1t2, No m1m2_c) = No (\sup => case sup of
        (AlphaEquivalentArrow t1t2' m1m2) => m1m2_c m1m2
    )
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (No t1t2_c, No m1m2_c) = No (\sup => case sup of
        (AlphaEquivalentArrow t1t2' m1m2) => m1m2_c m1m2
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) AExprPostulate = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprLambda x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprVariable x) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprApp x y) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprDefApp x xs) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) AExprStar = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) AExprBox = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )



isAlphaEquivalent (AExprApp x y) (AExprApp z w) with (isAlphaEquivalent x z)
    isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (Yes xz) with (isAlphaEquivalent y w)
        isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (Yes xz) | (Yes yw) = Yes (AlphaEquivalentApp xz yw)
        isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (Yes xz) | (No contra_yw) = No (\sup => case sup of
            (AlphaEquivalentApp xz' yw) => contra_yw yw
        )
    isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (No contra_xz) = No (\sup => case sup of
        (AlphaEquivalentApp xz yw) => contra_xz xz
    )

isAlphaEquivalent (AExprApp x y) AExprPostulate = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprLambda z w) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprVariable z) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprDefApp z xs) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) AExprStar = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) AExprBox = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprArrow z w) = No (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
