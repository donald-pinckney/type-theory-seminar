module defs.DerivationRules

import defs.AST
import defs.BindingDepth
import defs.Identifier
import Shared.ParseUtils
import defs.BindingDepth

import Data.Fin
import Data.So

%default total

public export
data Context : Nat -> Nat -> Type where
    Nil : Context ed Z
    (::) : AExpr (ed, cd) -> Context ed cd -> Context ed (S cd)

public export
record TypeJudgment where
    constructor MkTypeJudgment
    context : Context ed cd
    term : AExpr (ed, cd)
    type : AExpr (ed, cd)

infixr 10 |-
public export
(|-) : Context ed cd -> (AExpr (ed, cd), AExpr (ed, cd)) -> TypeJudgment
(|-) x (a, b) = MkTypeJudgment x a b


public export
deBruijnS : Fin (S cd) -> DeBruijnIdentifier cd -> DeBruijnIdentifier (S cd)
deBruijnS binderDepth (MkDeBruijnIdentifier deBruijn sourceId) =
    case (weaken deBruijn) >= binderDepth of
        True => MkDeBruijnIdentifier (FS deBruijn) sourceId
        False => MkDeBruijnIdentifier (weaken deBruijn) sourceId

mutual
    public export
    exprDepthS : Fin (S cd) -> AExpr (ed, cd) -> AExpr (ed, S cd)
    exprDepthS binderDepth AExprPostulate = AExprPostulate
    exprDepthS binderDepth (AExprLambda (MkADecl type sourceId) y) =
        let type' = exprDepthS binderDepth type in
        let y' = exprDepthS (FS binderDepth) y in
        AExprLambda (MkADecl type' sourceId) y'
    exprDepthS binderDepth (AExprVariable x) = AExprVariable (deBruijnS binderDepth x)
    exprDepthS binderDepth (AExprApp x y) = AExprApp (exprDepthS binderDepth x) (exprDepthS binderDepth y)
    -- exprDepthS binderDepth (AExprDefApp x xs) = AExprDefApp x (map (exprDepthS binderDepth) xs)
    exprDepthS binderDepth (AExprDefApp d xs) = AExprDefApp d (exprDepthS_defArgs binderDepth xs)
    exprDepthS binderDepth AExprStar = AExprStar
    exprDepthS binderDepth AExprBox = AExprBox
    exprDepthS binderDepth (AExprArrow (MkADecl type sourceId) y) =
        let type' = exprDepthS binderDepth type in
        let y' = exprDepthS (FS binderDepth) y in
        AExprArrow (MkADecl type' sourceId) y'

    public export
    exprDepthS_defArgs : Fin (S cd) -> List (AExpr (ed, cd)) -> List (AExpr (ed, S cd))
    exprDepthS_defArgs binderDepth [] = []
    exprDepthS_defArgs binderDepth (x :: xs) = (exprDepthS binderDepth x) :: (exprDepthS_defArgs binderDepth xs)


public export
dummy_Z_id : Identifier -> AExpr (ed, S cd)
dummy_Z_id id = AExprVariable $ MkDeBruijnIdentifier FZ id


--hack2 : (e1 : AExpr (ed, cd)) -> (e2 : AExpr (ed, cd)) -> (e1 == e2 = True) ->
--        e1 = e2

public export
data IsSort : AExpr d -> Type where
    SortStar : IsSort AExprStar
    SortBox : IsSort AExprBox

export
isSort : (e : AExpr d) -> Dec (IsSort e)
isSort AExprStar = Yes SortStar
isSort AExprBox = Yes SortBox
isSort AExprPostulate = ?isSort_rhs_1 -- Just a ton of boring contradictions to write
isSort (AExprLambda x y) = ?isSort_rhs_2
isSort (AExprVariable x) = ?isSort_rhs_3
isSort (AExprApp x y) = ?isSort_rhs_6
isSort (AExprDefApp x xs) = ?isSort_rhs_5
isSort (AExprArrow x y) = ?isSort_rhs_8

public export
data Holds : TypeJudgment -> Type where
    HackHolds : Holds $ gamma |- (e1, t1) -> So (e1 == e2) -> So (t1 == t2) -> Holds $ gamma |- (e2, t2)
    SortHolds : Holds $ [] |- (AExprStar, AExprBox)
    VarHolds : {src : Identifier} -> {isSort : IsSort s} -> (gamma : Context ed cd) ->
                (a : AExpr (ed, cd)) ->
                (Holds $ gamma |- (a, s)) ->
                Holds $ (a :: gamma) |- (dummy_Z_id src, exprDepthS FZ a)
    FormHolds : {src : Identifier} -> {isSort1 : IsSort s1} -> {isSort2 : IsSort s2} ->
                (gamma : Context ed cd) ->
                (a : AExpr (ed, cd)) ->
                (b : AExpr (ed, S cd)) ->
                (Holds $ gamma |- (a, s1)) ->
                (Holds $ (a :: gamma) |- (b, exprDepthS FZ s2)) ->
                Holds $ gamma |- (AExprArrow (MkADecl a src) b, s2)
