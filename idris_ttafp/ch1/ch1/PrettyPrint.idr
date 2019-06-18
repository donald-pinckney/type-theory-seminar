module ch1.PrettyPrint

import ch1.AST

%default total

export
prettyPrint : Term -> String
prettyPrint (Var (Bound k)) = show k
prettyPrint (Var (Free x)) = x
prettyPrint (App left@(Var v) right@(Var w)) = (prettyPrint left) ++ " " ++ (prettyPrint right)
prettyPrint (App left right@(Var w)) = "(" ++ (prettyPrint left) ++ ")" ++ (prettyPrint right)
prettyPrint (App left@(Var v) right) = (prettyPrint left) ++ "(" ++ (prettyPrint right) ++ ")"
prettyPrint (App left right) = "(" ++ (prettyPrint left) ++ ") (" ++ (prettyPrint right) ++ ")"
prettyPrint (Lambda lambdaBody) = "λ" ++ (prettyPrint lambdaBody)
