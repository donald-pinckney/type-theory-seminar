module defs.AST

import defs.Identifier
import defs.BindingDepth
import Data.Fin

public export
record DeBruijnIdentifier (len : Nat) where
    constructor MkDeBruijnIdentifier
    deBruijn : Fin len
    sourceId : Identifier

mutual
    public export
    record ADecl (depth : BindingDepth) where
        constructor MkADecl
        type : AExpr depth
        sourceId : Identifier

    public export
    data AExpr : (depth : BindingDepth) -> Type where
        AExprPostulate : AExpr depth
        AExprLambda : ADecl depth -> AExpr (ctxS depth) -> AExpr depth
        AExprVariable : DeBruijnIdentifier (ctxDepth depth) -> AExpr depth
        AExprApp : AExpr depth -> AExpr depth -> AExpr depth
        AExprDefApp : DeBruijnIdentifier (envDepth depth) -> List (AExpr depth) -> AExpr depth
        AExprStar : AExpr depth
        AExprBox : AExpr depth
        AExprArrow : ADecl depth -> AExpr (ctxS depth) -> AExpr depth

public export
record ADef (depth : BindingDepth) where
    constructor MkADef
    body : AExpr depth
    type : AExpr depth
    sourceId : Identifier
    sourceArgs : List Identifier

export
numArgs : ADef depth -> Nat
numArgs = length . sourceArgs

mutual
    public export
    record ASuppose (depth : BindingDepth) where
        constructor MkASuppose
        decl : ADecl depth
        body : ABook (ctxS depth)

    public export
    data ABook : (depth : BindingDepth) -> Type where
        ABookConsDef : ADef depth -> ABook (envS depth) -> ABook depth
        ABookConsSuppose : ASuppose depth -> ABook depth -> ABook depth
        ABookNil : ABook depth

public export
ARootBook : Type
ARootBook = ABook (Z, Z)



----------- Interface Implementations ------------

%access export
%default covering

Eq (DeBruijnIdentifier len) where
    (MkDeBruijnIdentifier deBruijn sourceId) == (MkDeBruijnIdentifier x y) = deBruijn == x

mutual
    Eq (ADecl depth) where
        (MkADecl type sourceId) == (MkADecl x y) = type == x

    Eq (AExpr depth) where
        AExprPostulate == AExprPostulate = True
        (AExprLambda x y) == (AExprLambda z w) = (x == z) && (y == w)
        (AExprVariable x) == (AExprVariable y) = x == y
        (AExprApp x y) == (AExprApp z w) = (x == z) && (y == w)
        AExprStar == AExprStar = True
        AExprBox == AExprBox = True
        (AExprArrow x y) == (AExprArrow z w) = (x == z) && (y == w)
        _ == _ = False

Eq (ADef depth) where
    a@(MkADef body type sourceId sourceArgs) == b@(MkADef x y z xs) = (body == x) && (type == y) && (numArgs a == numArgs b)

mutual
    Eq (ASuppose depth) where
        (MkASuppose decl body) == (MkASuppose x y) = (decl == x) && (body == y)

    Eq (ABook depth) where
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
    Show (ADecl depth) where
        show (MkADecl type sourceId) = (show sourceId) ++ " : " ++ (show type)

    Show (AExpr depth) where
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

Show (ADef depth) where
    show (MkADef body type sourceId sourceArgs) = makeTabs (ctxDepth depth) ++ show sourceId ++ "{" ++ showList sourceArgs ++ "} := " ++ show body ++ " : " ++ show type

mutual
    Show (ASuppose depth) where
        show (MkASuppose decl body) = makeTabs (ctxDepth depth) ++ "Suppose " ++ show decl ++ "\n" ++ show body

    Show (ABook depth) where
        show (ABookConsSuppose x y) = show x ++ (if y == ABookNil then "" else "\n\n") ++ show y
        show (ABookConsDef x y) = show x ++ (if y == ABookNil then "" else "\n") ++ show y
        show ABookNil = ""
