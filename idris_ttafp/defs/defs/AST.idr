module defs.AST

import defs.Identifier
import Data.Fin

public export
record DeBruijnIdentifier (len : Nat) where
    constructor MkDeBruijnIdentifier
    deBruijn : Fin len
    sourceId : Identifier

mutual
    public export
    record ADecl (envLen : Nat) (contextLen : Nat) where
        constructor MkADecl
        type : AExpr envLen contextLen
        sourceId : Identifier

    public export
    data AExpr : (envLen : Nat) -> (contextLen : Nat) -> Type where
        AExprPostulate : AExpr envLen contextLen
        AExprLambda : ADecl envLen contextLen -> AExpr envLen (S contextLen) -> AExpr envLen contextLen
        AExprVariable : DeBruijnIdentifier contextLen -> AExpr envLen contextLen
        AExprApp : AExpr envLen contextLen -> AExpr envLen contextLen -> AExpr envLen contextLen
        AExprDefApp : DeBruijnIdentifier envLen -> List (AExpr envLen contextLen) -> AExpr envLen contextLen
        AExprStar : AExpr envLen contextLen
        AExprBox : AExpr envLen contextLen
        AExprArrow : ADecl envLen contextLen -> AExpr envLen (S contextLen) -> AExpr envLen contextLen

public export
record ADef (envLen : Nat) (contextLen : Nat) where
    constructor MkADef
    body : AExpr envLen contextLen
    type : AExpr envLen contextLen
    sourceId : Identifier
    sourceArgs : List Identifier

export
numArgs : ADef envLen contextLen -> Nat
numArgs = length . sourceArgs

mutual
    public export
    record ASuppose (envLen : Nat) (contextLen : Nat) where
        constructor MkASuppose
        decl : ADecl envLen contextLen
        body : ABook envLen (S contextLen)

    public export
    data ABook : (envLen : Nat) -> (contextLen : Nat) -> Type where
        ABookConsDef : ADef envLen contextLen -> ABook (S envLen) contextLen -> ABook envLen contextLen
        ABookConsSuppose : ASuppose envLen contextLen -> ABook envLen contextLen -> ABook envLen contextLen
        ABookNil : ABook envLen contextLen

public export
ARootBook : Type
ARootBook = ABook Z Z



----------- Interface Implementations ------------

%access export
%default covering

Eq (DeBruijnIdentifier len) where
    (MkDeBruijnIdentifier deBruijn sourceId) == (MkDeBruijnIdentifier x y) = deBruijn == x

mutual
    Eq (ADecl envLen contextLen) where
        (MkADecl type sourceId) == (MkADecl x y) = type == x

    Eq (AExpr envLen contextLen) where
        AExprPostulate == AExprPostulate = True
        (AExprLambda x y) == (AExprLambda z w) = (x == z) && (y == w)
        (AExprVariable x) == (AExprVariable y) = x == y
        (AExprApp x y) == (AExprApp z w) = (x == z) && (y == w)
        AExprStar == AExprStar = True
        AExprBox == AExprBox = True
        (AExprArrow x y) == (AExprArrow z w) = (x == z) && (y == w)
        _ == _ = False

Eq (ADef envLen contextLen) where
    a@(MkADef body type sourceId sourceArgs) == b@(MkADef x y z xs) = (body == x) && (type == y) && (numArgs a == numArgs b)

mutual
    Eq (ASuppose envLen contextLen) where
        (MkASuppose decl body) == (MkASuppose x y) = (decl == x) && (body == y)

    Eq (ABook envLen contextLen) where
        (ABookConsDef x y) == (ABookConsDef z w) = (x == z) && (y == w)
        (ABookConsSuppose x y) == (ABookConsSuppose z w) = (x == z) && (y == w)
        ABookNil == ABookNil = True
        _ == _ = False



joinStrBy : String -> List String -> String
joinStrBy j [] = ""
joinStrBy j [x] = x
joinStrBy j (x :: xs) = x ++ j ++ (joinStrBy j xs)

showList : Show a => List a -> String
showList xs = joinStrBy ", " $ map show xs

Show (DeBruijnIdentifier len) where
    show (MkDeBruijnIdentifier deBruijn sourceId) = (show sourceId) ++ "↑" ++ (show $ finToNat deBruijn)

mutual
    Show (ADecl envLen contextLen) where
        show (MkADecl type sourceId) = (show sourceId) ++ " : " ++ (show type)

    Show (AExpr envLen contextLen) where
        show AExprPostulate = "?"
        show (AExprLambda x y) = "\\" ++ show x ++ " . " ++ show y
        show (AExprVariable x) = show x
        show (AExprApp x y) = "(" ++ show x ++ ") (" ++ show y ++ ")"
        show (AExprDefApp d args) = show d ++ " {" ++ showList args ++ "}"
        show AExprStar = "*"
        show AExprBox = "[]"
        show (AExprArrow x y) = "(" ++ show x ++ ") -> " ++ show y


makeTabs : Nat -> String
makeTabs n = joinStrBy "" $ take n (repeat "    ")

Show (ADef envLen contextLen) where
    show (MkADef body type sourceId sourceArgs) = makeTabs contextLen ++ show sourceId ++ "{" ++ showList sourceArgs ++ "} := " ++ show body ++ " : " ++ show type

mutual
    Show (ASuppose envLen contextLen) where
        show (MkASuppose decl body) = makeTabs contextLen ++ "Suppose " ++ show decl ++ "\n" ++ show body

    Show (ABook envLen contextLen) where
        show (ABookConsSuppose x y) = show x ++ "\n" ++ show y
        show (ABookConsDef x y) = show x ++ "\n" ++ show y
        show ABookNil = ""
