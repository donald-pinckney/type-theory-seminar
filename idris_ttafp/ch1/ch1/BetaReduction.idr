module ch1.BetaReduction

import ch1.AST
import ch1.Substitution
import ch1.BetaNormalForm

%default total

export
betaSingleStep : (input : Term) -> Either Term (InBNF input)
betaSingleStep (Var x) = Right BNFUnappliedVar
betaSingleStep (App (Var x) right) = case betaSingleStep right of
    (Left newRight) => Left $ App (Var x) newRight
    (Right right_bnf) => Right $ BNFVarApp right_bnf
betaSingleStep (App (App left_left left_right) right) =
    case betaSingleStep (App left_left left_right) of
    (Left newLeft) => Left $ App newLeft right
    (Right left_bnf) =>
        case betaSingleStep right of
        (Left newRight) => Left $ App (App left_left left_right) newRight
        (Right right_bnf) => Right $ BNFAppApp left_bnf right_bnf
betaSingleStep (App (Lambda lambdaBody) right) = Left $ substitute lambdaBody (Bound 0) right
betaSingleStep (Lambda lambdaBody) = case betaSingleStep lambdaBody of
    (Left newBody) => Left $ Lambda newBody
    (Right body_bnf) => Right (BNFLambda body_bnf)


export partial
betaMultiStep : Term -> (output : Term ** InBNF output)
betaMultiStep t = case betaSingleStep t of
    (Left newT) => betaMultiStep newT
    (Right t_bnf) => (t ** t_bnf)
