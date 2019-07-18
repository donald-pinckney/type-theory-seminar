module defs.AST

import defs.Identifier
import Data.Fin

public export
record DeBruijnIdentifier (len : Nat) where
    constructor MkDeBruijnIdentifier
    deBruijn : Fin len
    sourceId : Identifier

public export
data ResolvedIdentifier : (envLen : Nat) -> (contextLen : Nat) -> Type where
    Definition : DeBruijnIdentifier envLen -> ResolvedIdentifier envLen contextLen
    Context : DeBruijnIdentifier contextLen -> ResolvedIdentifier envLen contextLen

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
        AExprVariable : ResolvedIdentifier envLen contextLen -> AExpr envLen contextLen
        AExprApp : AExpr envLen contextLen -> AExpr envLen contextLen -> AExpr envLen contextLen
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

Eq (DeBruijnIdentifier len) where
    (MkDeBruijnIdentifier deBruijn sourceId) == (MkDeBruijnIdentifier x y) = deBruijn == x

Eq (ResolvedIdentifier envLen contextLen) where
    (Definition x) == (Definition y) = x == y
    (Context x) == (Context y) = x == y
    _ == _ = False

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


Show (DeBruijnIdentifier len) where
    show (MkDeBruijnIdentifier deBruijn sourceId) = (show sourceId) ++ " [" ++ (show $ finToNat deBruijn) ++ "]"

Show (ResolvedIdentifier envLen contextLen) where
    show (Definition x) = show x ++ "D"
    show (Context x) = show x ++ "C"

mutual
    Show (ADecl envLen contextLen) where
        show (MkADecl type sourceId) = (show sourceId) ++ " : " ++ (show type)

    Show (AExpr envLen contextLen) where
        show AExprPostulate = "POSTULATE"
        show (AExprLambda x y) = "\\" ++ show x ++ " . " ++ show y
        show (AExprVariable x) = show x
        show (AExprApp x y) = "(" ++ show x ++ ") (" ++ show y ++ ")"
        show AExprStar = "*"
        show AExprBox = "BOX"
        show (AExprArrow x y) = "(" ++ show x ++ ") -> " ++ show y

Show (ADef envLen contextLen) where
    show (MkADef body type sourceId sourceArgs) = show sourceId ++ "(" ++ show sourceArgs ++ ") := " ++ show body ++ " : " ++ show type

mutual
    Show (ASuppose envLen contextLen) where
        show (MkASuppose decl body) = "(Suppose " ++ show decl ++ show body ++ ")"

    Show (ABook envLen contextLen) where
        show (ABookConsSuppose x y) = show x ++ "\n" ++ show y
        show (ABookConsDef x y) = show x ++ "\n" ++ show y
        show ABookNil = ""
