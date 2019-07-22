module ch1.Substitution

import ch1.AST

%default total

export
substitute : (inTerm : Term) -> (replaceVar : Variable) -> (withTerm : Term) -> Term
substitute inTerm@(Var (Bound k)) (Bound j) withTerm = case decEq k j of
    (Yes prf) => withTerm
    (No contra) => inTerm

substitute inTerm@(Var (Bound k)) (Free x) withTerm = inTerm
substitute inTerm@(Var (Free x)) (Bound k) withTerm = inTerm
substitute inTerm@(Var (Free x)) (Free y) withTerm = case decEq x y of
    (Yes prf) => withTerm
    (No contra) => inTerm
substitute (App x y) replaceVar withTerm = App (substitute x replaceVar withTerm) (substitute y replaceVar withTerm)
substitute (Lambda lambdaBody) (Bound k) withTerm = Lambda (substitute lambdaBody (Bound (S k)) withTerm)
substitute (Lambda lambdaBody) (Free y) withTerm = Lambda (substitute lambdaBody (Free y) withTerm)
