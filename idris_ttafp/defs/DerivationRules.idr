module defs.DerivationRules

import defs.AST
import defs.BindingDepth
import Data.Fin
import defs.Identifier
import Shared.ParseUtils
import defs.BindingDepth

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
dummy_Z_id : SourceString -> AExpr (ed, S cd)
dummy_Z_id src = AExprVariable $ MkDeBruijnIdentifier FZ (MkIdentifier src)


--hack2 : (e1 : AExpr (ed, cd)) -> (e2 : AExpr (ed, cd)) -> (e1 == e2 = True) ->
--        e1 = e2


public export
data Holds : TypeJudgment -> Type where
--    HackHolds : Holds $ gamma |- (e1, t1) -> (e1 == e2 = True) -> (t1 == t2 =
--                                 True) -> Holds $ gamma |- (e2, t2)
    SortHolds : Holds $ [] |- (AExprStar, AExprBox)
    VarHolds : {src : SourceString} -> (gamma : Context ed cd) ->
                (a : AExpr (ed, cd)) ->
                Holds (gamma |- (a, s)) ->
                Holds $ (a :: gamma) |- (dummy_Z_id src, exprDepthS FZ a)
