module ch2.Substitution

import ch2.AST
import ch2.Context
import ch2.ContextLookup
import ch2.Judgments
import ch2.DerivationRules
import ElemAtIdx
import Data.So

%default total


export
substituteTerms : (inTerm : Term) -> (replaceVar : TermVariable) -> (withTerm : Term) -> Term
substituteTerms inTerm@(Var (Bound k)) (Bound j) withTerm = case decEq k j of
    (Yes prf) => withTerm
    (No contra) => inTerm

substituteTerms inTerm@(Var (Bound k)) (Free x) withTerm = inTerm
substituteTerms inTerm@(Var (Free x)) (Bound k) withTerm = inTerm
substituteTerms inTerm@(Var (Free x)) (Free y) withTerm = case decEq x y of
    (Yes prf) => withTerm
    (No contra) => inTerm
substituteTerms (App x y) replaceVar withTerm = App (substituteTerms x replaceVar withTerm) (substituteTerms y replaceVar withTerm)
substituteTerms (Lambda type lambdaBody) (Bound k) withTerm = Lambda type (substituteTerms lambdaBody (Bound (S k)) withTerm)
substituteTerms (Lambda type lambdaBody) (Free y) withTerm = Lambda type (substituteTerms lambdaBody (Free y) withTerm)



substituteBound : (inTerm : Term) -> (boundIdx : Nat) -> (withTerm : Term) -> Term


export
substituteTopBound : (inTerm : Term) -> (withTerm : Term) -> (bindIndex : Nat) ->
    Holds $ MkTypeJudgment (extraDecls ++ (push bindType gamma)) inTerm finalT ->
    Holds $ MkTypeJudgment gamma withTerm bindType ->
    length (extraDecls) = bindIndex ->
    (out : Term ** Holds $ MkTypeJudgment (extraDecls ++ gamma) out finalT)
substituteTopBound {finalT} {bindType} (Var (Bound n)) withTerm bindIndex b_t@(VarBound elemPrf) r_t extra_len =
    let same_t : (finalT = bindType) = ?eqewrqwe in
    case same_t of
    Refl =>
        case decEq n bindIndex of
        (Yes Refl) => (withTerm ** weakening r_t)
        (No contra) => (Var (Bound n) ** ?eqweeeeer)

substituteTopBound (Var (Free v)) withTerm bindIndex (VarFree keyPrf) r_t extra_len = (Var (Free v) ** VarFree ?eqwer)
substituteTopBound (App left right) withTerm bindIndex (ApplRule left_t right_t) r_t extra_len =
    let (outLeft ** outLeft_t) = substituteTopBound left withTerm bindIndex left_t r_t extra_len in
    let (outRight ** outRight_t) = substituteTopBound right withTerm bindIndex right_t r_t extra_len in
    (App outLeft outRight ** ApplRule outLeft_t outRight_t)
substituteTopBound {extraDecls} {gamma = gamma} {bindType = bindType} {finalT = (Arrow rho xi)} (Lambda rho body) withTerm bindIndex (AbstRule body_t) r_t extra_len =
    let body_t' : Holds (MkTypeJudgment ((rho :: extraDecls) ++ (push bindType gamma)) body xi) = ?eqwerqwer in
    let (newBody ** newBody_t) = substituteTopBound {extraDecls=rho :: extraDecls} body withTerm (S bindIndex) body_t' r_t (cong {f=S} extra_len) in
    let newBody_t' : Holds (MkTypeJudgment (push rho (extraDecls ++ gamma)) newBody xi) = ?opueqwer in
    (Lambda rho newBody ** AbstRule newBody_t')




export
substituteTopBound_pub : (inTerm : Term) -> (withTerm : Term) ->
    Holds $ MkTypeJudgment (push bindType gamma) inTerm finalT ->
    Holds $ MkTypeJudgment gamma withTerm bindType ->
    (out : Term ** Holds $ MkTypeJudgment gamma out finalT)
substituteTopBound_pub {gamma} {finalT} {bindType} inTerm withTerm in_t r_t =
    let in_t' : Holds (MkTypeJudgment ([] ++ push bindType gamma) inTerm finalT) =
        rewrite appCtxLeftNeutral (push bindType gamma) in
        in_t
    in
    rewrite sym $ appCtxLeftNeutral gamma in
    substituteTopBound {gamma=gamma} {extraDecls=[]} {finalT=finalT} inTerm withTerm Z in_t' r_t Refl


export
substitutionLemmaBound : Holds $ MkTypeJudgment (push bindType gamma) lambdaBody finalT ->
    Holds $ MkTypeJudgment gamma right bindType ->
    Holds $ MkTypeJudgment gamma (substituteTerms lambdaBody (Bound 0) right) finalT
substitutionLemmaBound {lambdaBody = (Var (Bound n))} (VarBound finalT_at_n) right_t =
    case decEq n 0 of
    (Yes Refl) => ?substitutionLemmaBound_rhs_1
    (No contra) => ?substitutionLemmaBound_rhs_6

substitutionLemmaBound {lambdaBody = (Var (Free v))} (VarFree x) right_t = ?substitutionLemmaBound_rhs_2
substitutionLemmaBound {lambdaBody = (App m n)} (ApplRule x y) right_t = ?substitutionLemmaBound_rhs_3
substitutionLemmaBound {lambdaBody = (Lambda sigma m)} (AbstRule x) right_t = ?substitutionLemmaBound_rhs_4
