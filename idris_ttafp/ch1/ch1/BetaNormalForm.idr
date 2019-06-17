module ch1.BetaNormalForm

import ch1.AST

%default total

public export
data InBNF : Term -> Type where
    BNFUnappliedVar : InBNF (Var x)
    BNFLambda : InBNF lambdaBody -> InBNF (Lambda lambdaBody)
    BNFVarApp : InBNF right -> InBNF (App (Var x) right)
    BNFAppApp : InBNF (App left_left left_right) -> InBNF right -> InBNF (App (App left_left left_right) right)

appSubtermBNF : InBNF (App left right) -> (InBNF left, InBNF right)
appSubtermBNF (BNFVarApp right_bnf) = (BNFUnappliedVar, right_bnf)
appSubtermBNF (BNFAppApp left_bnf right_bnf) = (left_bnf, right_bnf)

lambdaBodyBNF : InBNF (Lambda lambdaBody) -> InBNF lambdaBody
lambdaBodyBNF (BNFLambda body_bnf) = body_bnf

lambdaAppNotBNF : Not (InBNF (App (Lambda lambdaBody) right))
lambdaAppNotBNF BNFUnappliedVar impossible
lambdaAppNotBNF (BNFLambda _) impossible
lambdaAppNotBNF (BNFVarApp _) impossible
lambdaAppNotBNF (BNFAppApp _ _) impossible

export
isInBNF : (t : Term) -> Dec (InBNF t)
isInBNF (Var x) = Yes BNFUnappliedVar
isInBNF (App (Var x) right) =
    case isInBNF right of
        (Yes right_bnf) => Yes (BNFVarApp right_bnf)
        (No contra) => No $ contra . snd . appSubtermBNF

isInBNF (App (App left_left left_right) right) =
    case isInBNF (App left_left left_right) of
    (No left_not_bnf) => No $ left_not_bnf . fst . appSubtermBNF
    (Yes left_bnf) =>
        case isInBNF right of
        (No right_not_bnf) => No $ right_not_bnf . snd . appSubtermBNF
        (Yes right_bnf) => Yes (BNFAppApp left_bnf right_bnf)

isInBNF (App (Lambda lambdaBody) right) = No lambdaAppNotBNF
isInBNF (Lambda lambdaBody) =
    case isInBNF lambdaBody of
        (Yes body_bnf) => Yes (BNFLambda body_bnf)
        (No body_not_bnf) => No $ body_not_bnf . lambdaBodyBNF
