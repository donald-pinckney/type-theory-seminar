module ch2.BetaReduction

import ch2.AST
import ch2.Substitution
import ch2.BetaNormalForm
import ch2.Judgments
import ch2.DerivationRules
import ch2.Context

%default total

export
betaSingleStep : (input : Term) -> Holds $ MkTypeJudgment gamma input sigma -> Either (out : Term ** Holds $ MkTypeJudgment gamma out sigma) (InBNF input)
betaSingleStep (Var x) j = Right BNFUnappliedVar
betaSingleStep {gamma} {sigma=tau} (App (Var x) right) (ApplRule {sigma} left_arr right_sigma) =
    case betaSingleStep right right_sigma of
    (Left (newRight ** newRight_sigma)) => Left (App (Var x) newRight ** ApplRule left_arr newRight_sigma)
    (Right right_bnf) => Right $ BNFVarApp right_bnf
betaSingleStep {gamma} {sigma = finalT} (App (App left_left left_right) right) (ApplRule {sigma=rightT} left_arr right_t) =
    case betaSingleStep (App left_left left_right) left_arr of
    (Left (newLeft ** newLeft_arr)) => Left (App newLeft right ** ApplRule newLeft_arr right_t)
    (Right left_bnf) =>
        case betaSingleStep right right_t of
        (Left (newRight ** newRight_t)) => Left (App (App left_left left_right) newRight ** ApplRule left_arr newRight_t)
        (Right right_bnf) => Right $ BNFAppApp left_bnf right_bnf

betaSingleStep {gamma = gamma} {sigma=finalT} (App (Lambda bindType lambdaBody) right) (ApplRule (AbstRule x) right_t) = --?qwerqwer_2
    Left (substituteTerms lambdaBody (Bound 0) right ** ?eqwer)

betaSingleStep {gamma} {sigma = (Arrow bindType tau)} (Lambda bindType lambdaBody) (AbstRule body_tau) =
    case betaSingleStep lambdaBody body_tau of
    (Left (newBody ** newBody_tau)) => Left (Lambda bindType newBody ** AbstRule newBody_tau)
    (Right body_bnf) => Right (BNFLambda body_bnf)


export partial
betaMultiStep : (input : Term) -> Holds $ MkTypeJudgment gamma input sigma -> (output : Term ** (InBNF output, Holds $ MkTypeJudgment gamma output sigma))
betaMultiStep t j = case betaSingleStep t j of
    (Left (output ** output_t)) => betaMultiStep output output_t
    (Right t_bnf) => (t ** (t_bnf, j))
