module ch2.TypeCheck

import ch2.AST
import ch2.Context
import ch2.Judgments
import ch2.DerivationRules
import ch2.ContextLookup
import ElemAtIdx

%default total




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
lookupWrongFreeType {sigma} {gamma=MkContext (fds ** unique) bds} sigma_neq_tau keyPrf = \holds =>
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
        (VarFree ThisKey) =>(uniquenessContradiction {y=sigma} tail_key) unique



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
    (Yes (Arrow sigma tau ** leftArrow)) =>
        case findType gamma right of
        (Yes (eta ** rightEta)) =>
            case decEq eta sigma of
            (Yes Refl) => Yes (tau ** ApplRule leftArrow rightEta)
            (No eta_neq_sigma) => No (\(beta ** holds) =>
                case holds of
                (ApplRule {sigma=leftType} leftArrow' rightHolds') =>
                    let eta_leftType = uniqueType rightHolds' rightEta in
                    let left_arrows_eq = uniqueType leftArrow leftArrow' in
                    case left_arrows_eq of Refl => eta_neq_sigma (sym eta_leftType))
        (No rightNoType) => No (\(beta ** holds) => rightNoType $ rightTypeable holds)

    (Yes (VarType eta ** leftEta)) => No (\(tau ** holds) =>
        let (sigma ** leftHolds) = leftTypeable holds in
        case uniqueType leftEta leftHolds of Refl impossible
        )
    (No leftNoType) => No (\(tau ** holds) =>
        let (sigma ** leftHolds) = leftTypeable holds in
        leftNoType (Arrow sigma tau ** leftHolds))

findType gamma (Lambda sigma body) =
    case findType (push sigma gamma) body of
    (Yes (tau ** body_tau)) => Yes $ (Arrow sigma tau ** AbstRule body_tau)
    (No contra) => No (\(eta ** holds) =>
        case holds of (AbstRule {sigma} {tau} bodyHolds) => contra (tau ** bodyHolds))


checkTypeJudgment : (j : TypeJudgment) -> Dec (Holds j)
checkTypeJudgment (MkTypeJudgment gamma term sigma) =
    case findType gamma term of
    (Yes (sigma' ** holds')) =>
        case decEq sigma sigma' of
        (Yes Refl) => Yes holds'
        (No contra) => No (\holds => contra $ uniqueType holds holds')
    (No contra) => No (\holds => contra $ (sigma ** holds))
