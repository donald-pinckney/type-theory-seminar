module ch2.DerivationRules

import ch2.Context
import ch2.Judgments
import ch2.AST
import ElemAtIdx

%default total

public export
data Holds : TypeJudgment -> Type where
    VarBound : ElemAtIdx sigma (boundDecls gamma) n ->
        Holds $ MkTypeJudgment gamma (Var (Bound n)) sigma
    VarFree : ValueAtKey sigma (freeDecls gamma) v ->
        Holds $ MkTypeJudgment gamma (Var (Free v)) sigma
    ApplRule : Holds $ MkTypeJudgment gamma m (Arrow sigma tau) ->
        Holds $ MkTypeJudgment gamma n sigma ->
        Holds $ MkTypeJudgment gamma (App m n) tau
    AbstRule : Holds $ MkTypeJudgment (push sigma gamma) m tau ->
        Holds $ MkTypeJudgment gamma (Lambda sigma m) (Arrow sigma tau)


valueAtKeyImpliesElem : ValueAtKey x ps v -> FreeDeclarationListElem v ps
valueAtKeyImpliesElem ThisKey = Here
valueAtKeyImpliesElem (OtherKey unique tail_prf) = There (valueAtKeyImpliesElem tail_prf)

export
uniquenessContradiction : ValueAtKey x ps v -> Not (UniqueFreeDeclarations ((v, y) :: ps))
uniquenessContradiction = repeatNonUnique . valueAtKeyImpliesElem

uniqueElemAtIdx : ElemAtIdx x xs n -> ElemAtIdx y xs n -> x = y
uniqueElemAtIdx HereZ HereZ = Refl
uniqueElemAtIdx (ThereS later_x) (ThereS later_y) = uniqueElemAtIdx later_x later_y

uniqueValueAtKey : ValueAtKey x xs v -> ValueAtKey y xs v -> x = y
uniqueValueAtKey ThisKey ThisKey = Refl
uniqueValueAtKey {x} ThisKey (OtherKey unique keyPrf) = void $ (uniquenessContradiction {y=x} keyPrf) unique
uniqueValueAtKey {y} (OtherKey unique keyPrf) ThisKey = void $ (uniquenessContradiction {y=y} keyPrf) unique
uniqueValueAtKey (OtherKey uniqueLeft keyPrfLeft) (OtherKey uniqueRight keyPrfRight) = uniqueValueAtKey keyPrfLeft keyPrfRight


export
uniqueType : Holds $ MkTypeJudgment gamma m sigma -> Holds $ MkTypeJudgment gamma m tau -> sigma = tau
uniqueType (VarBound x) (VarBound y) = uniqueElemAtIdx x y
uniqueType (VarFree x) (VarFree y) = uniqueValueAtKey x y
uniqueType (ApplRule x z) (ApplRule y w) = case (uniqueType x y, uniqueType z w) of (Refl, Refl) => Refl
uniqueType (AbstRule x) (AbstRule y) = case uniqueType x y of Refl => Refl

export
leftTypeable : Holds $ MkTypeJudgment gamma (App left right) tau -> (sigma : Type' ** Holds $ MkTypeJudgment gamma left (Arrow sigma tau))
leftTypeable (ApplRule {sigma} leftHolds rightHolds) = (sigma ** leftHolds)

export
rightTypeable : Holds $ MkTypeJudgment gamma (App left right) tau -> (sigma : Type' ** Holds $ MkTypeJudgment gamma right sigma)
rightTypeable (ApplRule {sigma} _ rightHolds) = (sigma ** rightHolds)

export
weakening : Holds $ MkTypeJudgment gamma term sigma -> Holds $ MkTypeJudgment (extra ++ gamma) term sigma
