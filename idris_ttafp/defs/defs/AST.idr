module defs.AST

import defs.Identifier
import Data.Fin

export
record DeBruijnIdentifier (len : Nat) where
    constructor MkDeBruijnIdentifier
    deBruijn : Fin len
    sourceId : Identifier

public export
data ResolvedIdentifier : (envLen : Nat) -> (contextLen : Nat) -> Type where
    Definition : DeBruijnIdentifier envLen -> ResolvedIdentifier envLen contextLen
    Context : DeBruijnIdentifier contextLen -> ResolvedIdentifier envLen contextLen

mutual
    export
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

export
record ADef (envLen : Nat) (contextLen : Nat) where
    constructor MkADef
    body : AExpr envLen contextLen
    type : AExpr envLen contextLen
    sourceId : Identifier
    sourceArgs : List Identifier

numArgs : ADef envLen contextLen -> Nat
numArgs = length . sourceArgs

mutual
    export
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
