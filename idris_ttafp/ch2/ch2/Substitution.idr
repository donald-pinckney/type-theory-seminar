module ch2.Substitution

import ch2.AST
import ch2.Context
import ch2.ContextLookup
import ch2.Judgments
import ch2.DerivationRules

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


export
substitutionLemmaBound : Holds $ MkTypeJudgment (push bindType gamma) lambdaBody finalT ->
    Holds $ MkTypeJudgment gamma right bindType ->
    Holds $ MkTypeJudgment gamma (substituteTerms lambdaBody (Bound 0) right) finalT
substitutionLemmaBound x y = ?substitutionLemmaBound_rhs
