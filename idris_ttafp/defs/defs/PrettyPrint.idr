module defs.PrettyPrint

import defs.AST

%default total

export
prettyPrintType : Type' -> String
prettyPrintType (VarType (FreeType v)) = v
prettyPrintType (Arrow a@(VarType x) b) = (prettyPrintType a) ++ " -> " ++ (prettyPrintType b)
prettyPrintType (Arrow a b) = "(" ++ (prettyPrintType a) ++ " -> " ++ (prettyPrintType b) ++ ")"

export
prettyPrintTerm : Term -> String
prettyPrintTerm (Var (Bound k)) = show k
prettyPrintTerm (Var (Free x)) = x
prettyPrintTerm (App left@(Var v) right@(Var w)) = (prettyPrintTerm left) ++ " " ++ (prettyPrintTerm right)
prettyPrintTerm (App left right@(Var w)) = "(" ++ (prettyPrintTerm left) ++ ")" ++ (prettyPrintTerm right)
prettyPrintTerm (App left@(Var v) right) = (prettyPrintTerm left) ++ "(" ++ (prettyPrintTerm right) ++ ")"
prettyPrintTerm (App left right) = "(" ++ (prettyPrintTerm left) ++ ") (" ++ (prettyPrintTerm right) ++ ")"
prettyPrintTerm (Lambda type lambdaBody) = "λ" ++ (prettyPrintType type) ++ " . " ++ (prettyPrintTerm lambdaBody)
