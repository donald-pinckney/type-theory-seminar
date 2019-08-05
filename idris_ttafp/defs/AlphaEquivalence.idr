module defs.AlphaEquivalence

import defs.Identifier
import defs.BindingDepth
import Data.Fin
import Data.So
import Decidable.Order
import defs.AST
import defs.ResultDec

%default total


public export
data AllEquiv : (p : t -> t -> Type) -> List t -> List t -> Type where
    ConsEquiv : p h1 h2 -> AllEquiv p rest1 rest2 -> AllEquiv p (h1 :: rest1) (h2 :: rest2)
    NilEquiv : AllEquiv p [] []

export
implementation Preorder t p => Preorder (List t) (AllEquiv p) where
    reflexive [] = NilEquiv
    reflexive (x :: xs) = ConsEquiv (reflexive x) (reflexive xs)

    transitive (h1 :: rest1) (h2 :: rest2) (h3 :: rest3) (ConsEquiv h1h2 rest1rest2) (ConsEquiv h2h3 rest2rest3) = ConsEquiv (transitive h1 h2 h3 h1h2 h2h3) (transitive rest1 rest2 rest3 rest1rest2 rest2rest3)
    transitive [] [] [] NilEquiv NilEquiv = NilEquiv

export
implementation Equivalence t p => Equivalence (List t) (AllEquiv p) where
    symmetric (h1 :: rest1) (h2 :: rest2) (ConsEquiv h1h2 rest1rest2) = ConsEquiv (symmetric h1 h2 h1h2) (symmetric rest1 rest2 rest1rest2)
    symmetric [] [] NilEquiv = NilEquiv

msg : String
msg = "not alpha equivalent"

export
isAllEquiv : (xs : List t) -> (ys : List t) -> ((x : t) -> (y : t) -> ResultDec (p x y)) -> ResultDec (AllEquiv p xs ys)
isAllEquiv [] [] isEquiv = Ok NilEquiv
isAllEquiv (x :: xs) (y :: ys) isEquiv = case (isEquiv x y, isAllEquiv xs ys isEquiv) of
    (Ok xy, Ok xsys) => Ok (ConsEquiv xy xsys)
    (Error msg1 xy_c, Ok xsys) => Error msg (\sup => case sup of
        (ConsEquiv xy xsys') => xy_c xy
    )
    (Ok xy, Error msg2 xsys_c) => Error msg (\sup => case sup of
        (ConsEquiv xy' xsys) => xsys_c xsys
    )
    (Error msg1 xy_c, Error msg2 xsys_c) => Error msg (\sup => case sup of
        (ConsEquiv xy xsys') => xy_c xy
    )
isAllEquiv (x :: xs) [] isEquiv = Error msg (\sup => case sup of
    (ConsEquiv _ _) impossible
    NilEquiv impossible
)
isAllEquiv [] (y :: ys) isEquiv = Error msg (\sup => case sup of
    (ConsEquiv _ _) impossible
    NilEquiv impossible
)

public export
data AlphaEquivalent : AExpr d -> AExpr d -> Type where
    AlphaEquivalentPostulate : AlphaEquivalent AExprPostulate AExprPostulate
    AlphaEquivalentStar : AlphaEquivalent AExprStar AExprStar
    AlphaEquivalentBox : AlphaEquivalent AExprBox AExprBox
    AlphaEquivalentVariable : AlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x src1)) (AExprVariable (MkDeBruijnIdentifier x src2))
    AlphaEquivalentLambda : AlphaEquivalent t1 t2 -> AlphaEquivalent m1 m2 -> AlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2)
    AlphaEquivalentArrow : AlphaEquivalent t1 t2 -> AlphaEquivalent m1 m2 -> AlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2)
    AlphaEquivalentDefApp : AllEquiv AlphaEquivalent args1 args2 -> AlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x src1) args1) (AExprDefApp (MkDeBruijnIdentifier x src2) args2)
    AlphaEquivalentApp : AlphaEquivalent l1 l2 -> AlphaEquivalent r1 r2 -> AlphaEquivalent (AExprApp l1 r1) (AExprApp l2 r2)

public export
implementation Preorder (AExpr d) AlphaEquivalent where
    reflexive AExprPostulate = AlphaEquivalentPostulate
    reflexive AExprStar = AlphaEquivalentStar
    reflexive AExprBox = AlphaEquivalentBox
    reflexive (AExprApp x y) = AlphaEquivalentApp (reflexive x) (reflexive y)
    reflexive (AExprLambda (MkADecl t src) m) = AlphaEquivalentLambda (reflexive t) (reflexive m)
    reflexive (AExprVariable (MkDeBruijnIdentifier x src)) = AlphaEquivalentVariable
    reflexive (AExprArrow (MkADecl t src) m) = AlphaEquivalentArrow (reflexive t) (reflexive m)
    reflexive (AExprDefApp (MkDeBruijnIdentifier x src) args) = AlphaEquivalentDefApp (assert_total (reflexive args))


    transitive AExprPostulate AExprPostulate AExprPostulate AlphaEquivalentPostulate AlphaEquivalentPostulate = AlphaEquivalentPostulate
    transitive AExprStar AExprStar AExprStar AlphaEquivalentStar AlphaEquivalentStar = AlphaEquivalentStar
    transitive AExprBox AExprBox AExprBox AlphaEquivalentBox AlphaEquivalentBox = AlphaEquivalentBox
    transitive (AExprVariable (MkDeBruijnIdentifier x src1)) (AExprVariable (MkDeBruijnIdentifier x src2)) (AExprVariable (MkDeBruijnIdentifier x src3)) AlphaEquivalentVariable AlphaEquivalentVariable = AlphaEquivalentVariable
    transitive (AExprApp l1 r1) (AExprApp l2 r2) (AExprApp l3 r3) (AlphaEquivalentApp l1l2 r1r2) (AlphaEquivalentApp l2l3 r2r3) = AlphaEquivalentApp (transitive l1 l2 l3 l1l2 l2l3) (transitive r1 r2 r3 r1r2 r2r3)
    transitive (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) (AExprLambda (MkADecl t3 src3) m3) (AlphaEquivalentLambda t1t2 m1m2) (AlphaEquivalentLambda t2t3 m2m3) = AlphaEquivalentLambda (transitive t1 t2 t3 t1t2 t2t3) (transitive m1 m2 m3 m1m2 m2m3)
    transitive (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) (AExprArrow (MkADecl t3 src3) m3) (AlphaEquivalentArrow t1t2 m1m2) (AlphaEquivalentArrow t2t3 m2m3) = AlphaEquivalentArrow (transitive t1 t2 t3 t1t2 t2t3) (transitive m1 m2 m3 m1m2 m2m3)
    transitive (AExprDefApp (MkDeBruijnIdentifier x src1) args1) (AExprDefApp (MkDeBruijnIdentifier x src2) args2) (AExprDefApp (MkDeBruijnIdentifier x src3) args3) (AlphaEquivalentDefApp args1args2) (AlphaEquivalentDefApp args2args3) = AlphaEquivalentDefApp (assert_total (transitive args1 args2 args3 args1args2 args2args3))

public export
implementation Equivalence (AExpr d) AlphaEquivalent where
    symmetric AExprPostulate AExprPostulate AlphaEquivalentPostulate = AlphaEquivalentPostulate
    symmetric AExprStar AExprStar AlphaEquivalentStar = AlphaEquivalentStar
    symmetric AExprBox AExprBox AlphaEquivalentBox = AlphaEquivalentBox
    symmetric (AExprVariable (MkDeBruijnIdentifier x src1)) (AExprVariable (MkDeBruijnIdentifier x src2)) AlphaEquivalentVariable = AlphaEquivalentVariable
    symmetric (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) (AlphaEquivalentLambda t1t2 m1m2) = AlphaEquivalentLambda (symmetric t1 t2 t1t2) (symmetric m1 m2 m1m2)
    symmetric (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) (AlphaEquivalentArrow t1t2 m1m2) = AlphaEquivalentArrow (symmetric t1 t2 t1t2) (symmetric m1 m2 m1m2)
    symmetric (AExprDefApp (MkDeBruijnIdentifier x src1) args1) (AExprDefApp (MkDeBruijnIdentifier x src2) args2) (AlphaEquivalentDefApp args1args2) = AlphaEquivalentDefApp (assert_total (symmetric args1 args2 args1args2))
    symmetric (AExprApp l1 r1) (AExprApp l2 r2) (AlphaEquivalentApp l1l2 r1r2) = AlphaEquivalentApp (symmetric l1 l2 l1l2) (symmetric r1 r2 r1r2)




export
isAlphaEquivalent : (e1 : AExpr d) -> (e2 : AExpr d) -> ResultDec (AlphaEquivalent e1 e2)
isAlphaEquivalent AExprPostulate AExprPostulate = Ok AlphaEquivalentPostulate
isAlphaEquivalent AExprPostulate (AExprLambda x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprVariable x) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprApp x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprDefApp x xs) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate AExprStar = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate AExprBox = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprPostulate (AExprArrow x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )

isAlphaEquivalent AExprStar AExprStar = Ok AlphaEquivalentStar
isAlphaEquivalent AExprStar AExprPostulate = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprLambda x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprVariable x) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprApp x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprDefApp x xs) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar AExprBox = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprStar (AExprArrow x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )


isAlphaEquivalent AExprBox AExprBox = Ok AlphaEquivalentBox
isAlphaEquivalent AExprBox AExprPostulate = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprLambda x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprVariable x) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprApp x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprDefApp x xs) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox AExprStar = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent AExprBox (AExprArrow x y) = Error msg (\pi_arg => case pi_arg of
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
    (Yes Refl) => Ok AlphaEquivalentVariable
    (No contra) => Error msg (\sup => case sup of
        AlphaEquivalentVariable => contra Refl
    )

isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) AExprPostulate = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprLambda x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprApp x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprDefApp x xs) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) AExprStar = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) AExprBox = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprVariable (MkDeBruijnIdentifier x1 src1)) (AExprArrow x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )


isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) with (decEq x1 x2, assert_total (isAllEquiv args1 args2 isAlphaEquivalent))
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (Yes x1x2, Ok args1args2) = rewrite x1x2 in Ok (AlphaEquivalentDefApp args1args2)
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (No x1x2_c, Ok args1args2) = Error msg (\sup => case sup of
        (AlphaEquivalentDefApp args1args2') => x1x2_c Refl
    )
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (Yes x1x2, Error msg2 args1args2_c) = Error msg (\sup => case sup of
        (AlphaEquivalentDefApp args1args2) => args1args2_c args1args2
    )
    isAlphaEquivalent (AExprDefApp (MkDeBruijnIdentifier x1 src1) args1) (AExprDefApp (MkDeBruijnIdentifier x2 src2) args2) | (No x1x2_c, Error msg2 args1args2_c) = Error msg (\sup => case sup of
        (AlphaEquivalentDefApp args1args2) => args1args2_c args1args2
    )

isAlphaEquivalent (AExprDefApp x args) AExprPostulate = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprLambda y z) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprVariable y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprApp y z) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) AExprStar = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) AExprBox = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprDefApp x args) (AExprArrow y z) = Error msg (\pi_arg => case pi_arg of
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
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (Ok t1t2, Ok m1m2) = Ok (AlphaEquivalentLambda t1t2 m1m2)
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (Error msg1 t1t2_c, Ok m1m2) = Error msg (\sup => case sup of
        (AlphaEquivalentLambda t1t2 m1m2') => t1t2_c t1t2
    )
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (Ok t1t2, Error msg2 m1m2_c) = Error msg (\sup => case sup of
        (AlphaEquivalentLambda t1t2' m1m2) => m1m2_c m1m2
    )
    isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) | (Error msg1 t1t2_c, Error msg2 m1m2_c) = Error msg (\sup => case sup of
        (AlphaEquivalentLambda t1t2' m1m2) => m1m2_c m1m2
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) AExprPostulate = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprArrow x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprVariable x) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprApp x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) (AExprDefApp x xs) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) AExprStar = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprLambda (MkADecl t1 src1) m1) AExprBox = Error msg (\pi_arg => case pi_arg of
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
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (Ok t1t2, Ok m1m2) = Ok (AlphaEquivalentArrow t1t2 m1m2)
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (Error msg1 t1t2_c, Ok m1m2) = Error msg (\sup => case sup of
        (AlphaEquivalentArrow t1t2 m1m2') => t1t2_c t1t2
    )
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (Ok t1t2, Error msg2 m1m2_c) = Error msg (\sup => case sup of
        (AlphaEquivalentArrow t1t2' m1m2) => m1m2_c m1m2
    )
    isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) | (Error msg1 t1t2_c, Error msg2 m1m2_c) = Error msg (\sup => case sup of
        (AlphaEquivalentArrow t1t2' m1m2) => m1m2_c m1m2
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) AExprPostulate = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprLambda x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprVariable x) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprApp x y) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) (AExprDefApp x xs) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) AExprStar = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprArrow (MkADecl t1 src1) m1) AExprBox = Error msg (\pi_arg => case pi_arg of
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
    isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (Ok xz) with (isAlphaEquivalent y w)
        isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (Ok xz) | (Ok yw) = Ok (AlphaEquivalentApp xz yw)
        isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (Ok xz) | (Error msg1 contra_yw) = Error msg (\sup => case sup of
            (AlphaEquivalentApp xz' yw) => contra_yw yw
        )
    isAlphaEquivalent (AExprApp x y) (AExprApp z w) | (Error msg1 contra_xz) = Error msg (\sup => case sup of
        (AlphaEquivalentApp xz yw) => contra_xz xz
    )

isAlphaEquivalent (AExprApp x y) AExprPostulate = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprLambda z w) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprVariable z) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprDefApp z xs) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) AExprStar = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) AExprBox = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
isAlphaEquivalent (AExprApp x y) (AExprArrow z w) = Error msg (\pi_arg => case pi_arg of
        AlphaEquivalentPostulate impossible
        AlphaEquivalentStar impossible
        AlphaEquivalentBox impossible
        AlphaEquivalentVariable impossible
        (AlphaEquivalentLambda _ _) impossible
        (AlphaEquivalentArrow _ _) impossible
        (AlphaEquivalentDefApp _) impossible
        (AlphaEquivalentApp _ _) impossible
    )
