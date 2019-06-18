module ch2.TypeCheck

import ch2.AST
import ch2.Context
import ch2.Judgments
import ch2.DerivationRules
import ch2.ContextLookup
import ElemAtIdx


valueAtKeyImpliesElem : ValueAtKey x ps v -> FreeDeclarationListElem v ps
valueAtKeyImpliesElem ThisKey = Here
valueAtKeyImpliesElem (OtherKey unique tail_prf) = There (valueAtKeyImpliesElem tail_prf)

uniquenessContradiction : ValueAtKey x ps v -> Not (UniqueFreeDeclarations ((v, y) :: ps))
uniquenessContradiction = repeatNonUnique . valueAtKeyImpliesElem


lookupWrongBoundType : Not (sigma = tau) ->
    ElemAtIdx tau (boundDecls gamma) n ->
    Not (Holds $ MkTypeJudgment gamma (Var (Bound n)) sigma)

lookupWrongBoundType {gamma=MkContext fds (tau :: bds)} sigma_neq_tau HereZ = \holds =>
    case holds of (VarBound HereZ) => sigma_neq_tau Refl

lookupWrongBoundType {gamma=MkContext fds (eta :: bds)} sigma_neq_tau (ThereS tau_later) = \holds =>
    let ih = lookupWrongBoundType {gamma=MkContext fds bds} sigma_neq_tau tau_later in
    case holds of
    (VarBound (ThereS sigma_later)) =>
        let holds_later = VarBound {gamma=MkContext fds bds} sigma_later in
        ih holds_later


lookupWrongFreeType : Not (sigma = tau) ->
    ValueAtKey tau (freeDecls gamma) v ->
    Not (Holds $ MkTypeJudgment gamma (Var (Free v)) sigma)
lookupWrongFreeType {gamma=MkContext (fds ** unique) bds} sigma_neq_tau keyPrf = \holds =>
    case keyPrf of
    ThisKey =>
        case holds of
        (VarFree ThisKey) => sigma_neq_tau Refl
        (VarFree (OtherKey alsoUnique keyPrf_sigma)) => uniquenessContradiction keyPrf_sigma unique

    (OtherKey {p=hd} {xs=fds_tail} _ tail_key) =>
        let ih = lookupWrongFreeType {gamma=MkContext (fds_tail ** uniqueUnCons unique) bds} sigma_neq_tau tail_key in
        case holds of
        (VarFree (OtherKey _ sigma_later)) =>
            let holds_later = VarFree {gamma=MkContext (fds_tail ** uniqueUnCons unique) bds} sigma_later in
            ih holds_later


findType : (gamma : Context) -> (term : Term) -> Dec (sigma : Type' ** Holds $ MkTypeJudgment gamma term sigma)
findType gamma (Var (Bound n)) =
    case contextLookupBoundDecl gamma n of
    (Yes (sigma ** elemPrf)) => Yes (sigma ** VarBound elemPrf)
    (No outOfBounds) => No $ (\holds => case holds of (sigma ** VarBound elemIdx) => outOfBounds (sigma ** elemIdx))

findType gamma (Var (Free v)) =
    case contextLookupFreeDecl gamma v of
    (Yes (sigma ** elemPrf)) => Yes (sigma ** VarFree elemPrf)
    (No outOfBounds) => No $ (\holds => case holds of (sigma ** VarFree elemIdx) => outOfBounds (sigma ** elemIdx))

findType gamma (App left right) =
    case findType gamma left of
    (Yes prf) => ?findType_rhs_1
    (No contra) => ?findType_rhs_4

findType gamma (Lambda type body) = ?findType_rhs_3


checkTypeJudgment : (j : TypeJudgment) -> Dec (Holds j)
checkTypeJudgment (MkTypeJudgment gamma (Var (Bound n)) sigma) =
    case contextLookupBoundDecl gamma n of
    (Yes (tau ** elemPrf)) =>
        case decEq sigma tau of
        (Yes Refl) => Yes $ VarBound elemPrf
        (No sigma_neq_tau) => No $ lookupWrongBoundType sigma_neq_tau elemPrf
    (No outOfBounds) => No $ (\holds => case holds of (VarBound elemIdx) => outOfBounds (sigma ** elemIdx))

checkTypeJudgment (MkTypeJudgment gamma (Var (Free v)) sigma) =
    case contextLookupFreeDecl gamma v of
    (Yes (tau ** keyPrf)) =>
        case decEq sigma tau of
            (Yes Refl) => Yes $ VarFree keyPrf
            (No sigma_neq_tau) => No $ lookupWrongFreeType sigma_neq_tau keyPrf
    (No noKey) => No $ (\holds => case holds of (VarFree keyPrf) => noKey (sigma ** keyPrf))

checkTypeJudgment (MkTypeJudgment gamma (App left right) tau) = ?checkTypeJudgment_rhs_3
checkTypeJudgment (MkTypeJudgment gamma (Lambda bindType body) sigma) = ?checkTypeJudgment_rhs_4
