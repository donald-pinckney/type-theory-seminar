module defs.DerivationRules

import defs.AST
import defs.BindingDepth
import defs.Identifier
import Shared.ParseUtils
import defs.BindingDepth
import defs.AlphaEquivalence
import defs.ResultDec
import defs.BetaEquivalence

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


export
implementation Show (Context ed cd) where
  show [] = ""
  show (t :: Nil) = assert_total (show t)
  show (t :: ts) = assert_total (show t) ++ ", " ++ show ts

export
implementation Show TypeJudgment where
  show (MkTypeJudgment context term type) = show context ++ " |- " ++ assert_total (show term) ++ " : " ++ assert_total (show type)



-- export
-- exprDepthPrev : (binderDepth : Fin (S cd)) -> (bigE : AExpr (ed, S cd)) -> (smallE : AExpr (ed, cd) ** (exprDepthS binderDepth smallE = bigE))
-- exprDepthPrev binderDepth AExprPostulate = (AExprPostulate ** Refl)
-- exprDepthPrev binderDepth AExprStar = (AExprStar ** Refl)
-- exprDepthPrev binderDepth AExprBox = (AExprBox ** Refl)
-- exprDepthPrev binderDepth (AExprApp x y) = case (exprDepthPrev binderDepth x, exprDepthPrev binderDepth y) of
--     ((px ** Refl), (py ** Refl)) => (AExprApp px py ** Refl)
--
-- exprDepthPrev FZ (AExprVariable (MkDeBruijnIdentifier FZ sourceId)) = ?oiueprqew --(AExprVariable (MkDeBruijnIdentifier FZ sourceId) ** ?erqwer)
-- exprDepthPrev (FS x) (AExprVariable (MkDeBruijnIdentifier FZ sourceId)) = ?exprDepthPrev_rhs_6
-- exprDepthPrev binderDepth (AExprVariable (MkDeBruijnIdentifier (FS x) sourceId)) = ?exprDepthPrev_rhs_4
-- exprDepthPrev binderDepth (AExprLambda x y) = ?exprDepthPrev_rhs_2
-- exprDepthPrev binderDepth (AExprDefApp x xs) = ?exprDepthPrev_rhs_5
-- exprDepthPrev binderDepth (AExprArrow x y) = ?exprDepthPrev_rhs_8


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
isSort : (e : AExpr d) -> ResultDec (IsSort e)
isSort AExprStar = Ok SortStar
isSort AExprBox = Ok SortBox
isSort AExprPostulate = Error "postulate not sort" (\sup => case sup of
    SortStar impossible
    SortBox impossible
)
isSort (AExprLambda x y) = Error "lambda not sort" (\sup => case sup of
    SortStar impossible
    SortBox impossible
)
isSort (AExprVariable x) = Error "variable not sort" (\sup => case sup of
    SortStar impossible
    SortBox impossible
)
isSort (AExprApp x y) = Error "app not sort" (\sup => case sup of
    SortStar impossible
    SortBox impossible
)
isSort (AExprDefApp x xs) = Error "def app not sort" (\sup => case sup of
    SortStar impossible
    SortBox impossible
)
isSort (AExprArrow x y) = Error "arrow not sort" (\sup => case sup of
    SortStar impossible
    SortBox impossible
)


public export
data Holds : TypeJudgment -> Type where
    -- HackHolds : Holds $ gamma |- (e1, t1) -> AlphaEquivalent e1 e2 -> AlphaEquivalent t1 t2 -> Holds $ gamma |- (e2, t2)
    AlphaHolds : Holds $ gamma |- (a, b) ->
                AlphaEquivalent b b' ->
                Holds $ gamma |- (a, b')

    ConvHolds : {isSort : IsSort s} ->
                Holds $ gamma |- (a, b) ->
                Holds $ gamma |- (b', s) ->
                BetaEquivalent b b' ->
                Holds $ gamma |- (a, b')

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
    WeakHolds : {isSort : IsSort s} ->
                (Holds $ gamma |- (a, b)) ->
                (Holds $ gamma |- (c, s)) ->
                Holds $ (c :: gamma) |- (exprDepthS FZ a, exprDepthS FZ b)
    ApplHolds : {src : Identifier} ->
                (Holds $ gamma |- (m, AExprArrow (MkADecl a src) b)) ->
                (Holds $ gamma |- (n, a)) ->
                Holds $ gamma |- (AExprApp m n, substituteTop Z LTEZero b n)
    AbstHolds : {isSort : IsSort s} ->
                (Holds $ (a :: gamma) |- (m, b)) ->
                (Holds $ gamma |- (AExprArrow (MkADecl a src) b, s)) ->
                Holds $ gamma |- (AExprLambda (MkADecl a src) m, AExprArrow (MkADecl a src) b)
