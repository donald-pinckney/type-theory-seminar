module ch2.TypeCheck

import ch2.AST
import ch2.Context
import ch2.Judgments
import ch2.DerivationRules
import ch2.ContextLookup
import ElemAtIdx

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



checkTypeJudgment : (j : TypeJudgment) -> Dec (Holds j)
checkTypeJudgment (MkTypeJudgment gamma (Var (Bound n)) sigma) =
    case contextLookupBoundDecl gamma n of
    (Yes (tau ** elemPrf)) =>
        case decEq sigma tau of
        (Yes Refl) => Yes $ VarBound elemPrf
        (No sigma_neq_tau) => No $ lookupWrongBoundType sigma_neq_tau elemPrf
    (No outOfBounds) => ?checkTypeJudgment_rhs_6

checkTypeJudgment (MkTypeJudgment gamma (Var (Free x)) sigma) = ?checkTypeJudgment_rhs_5
checkTypeJudgment (MkTypeJudgment gamma (App left right) sigma) = ?checkTypeJudgment_rhs_3
checkTypeJudgment (MkTypeJudgment gamma (Lambda bindType body) sigma) = ?checkTypeJudgment_rhs_4
