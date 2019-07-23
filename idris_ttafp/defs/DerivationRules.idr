module defs.DerivationRules

import defs.AST
import defs.BindingDepth
import Data.Fin
import defs.Identifier
import Shared.ParseUtils
import defs.Environments

%default total

public export
data Context : Nat -> Type where
    Nil : Context Z
    (::) : AExpr (ed, cd) -> Context cd -> Context (S cd)

public export
record TypeJudgment where
    constructor MkTypeJudgment
    context : Context cd
    term : AExpr (ed, cd)
    type : AExpr (ed, cd)

infixr 10 |-
public export
(|-) : Context cd -> (AExpr (ed, cd), AExpr (ed, cd)) -> TypeJudgment
(|-) x (a, b) = MkTypeJudgment x a b


public export
dummy_Z_id : AExpr (ed, S cd)
dummy_Z_id = AExprVariable $ MkDeBruijnIdentifier FZ (MkIdentifier (unpackSource "__dummy__"))


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
data Holds : TypeJudgment -> Type where
    SortHolds : Holds $ [] |- (AExprStar, AExprBox)
    VarHolds : (gamma : Context cd) ->
                (a : AExpr (ed, cd)) ->
                Holds (gamma |- (a, s)) ->
                Holds $ (a :: gamma) |- (dummy_Z_id, exprDepthS FZ a)
