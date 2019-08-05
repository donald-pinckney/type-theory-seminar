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


public export
deBruijnInc : DeBruijnIdentifier cd -> DeBruijnIdentifier (S cd)
deBruijnInc (MkDeBruijnIdentifier deBruijn sourceId) = MkDeBruijnIdentifier (FS deBruijn) sourceId

public export
deBruijnS : Fin (S cd) -> DeBruijnIdentifier cd -> DeBruijnIdentifier (S cd)
-- deBruijnS : Fin (S cd) -> DeBruijnIdentifier cd

deBruijnS FZ (MkDeBruijnIdentifier deBruijn sourceId) = MkDeBruijnIdentifier (FS deBruijn) sourceId
deBruijnS (FS x) (MkDeBruijnIdentifier FZ sourceId) = MkDeBruijnIdentifier FZ sourceId
deBruijnS (FS binderDepth') (MkDeBruijnIdentifier (FS deBruijn') sourceId) =
    deBruijnInc $ deBruijnS binderDepth' (MkDeBruijnIdentifier deBruijn' sourceId)

-- deBruijnS binderDepth (MkDeBruijnIdentifier deBruijn sourceId) =
--     case (weaken deBruijn) >= binderDepth of
--         True => MkDeBruijnIdentifier (FS deBruijn) sourceId
--         False => MkDeBruijnIdentifier (weaken deBruijn) sourceId

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


export
exprDepthPrev : (binderDepth : Fin (S cd)) -> (bigE : AExpr (ed, S cd)) -> (smallE : AExpr (ed, cd) ** (exprDepthS binderDepth smallE = bigE))
exprDepthPrev binderDepth AExprPostulate = (AExprPostulate ** Refl)
exprDepthPrev binderDepth AExprStar = (AExprStar ** Refl)
exprDepthPrev binderDepth AExprBox = (AExprBox ** Refl)
exprDepthPrev binderDepth (AExprApp x y) = case (exprDepthPrev binderDepth x, exprDepthPrev binderDepth y) of
    ((px ** Refl), (py ** Refl)) => (AExprApp px py ** Refl)

exprDepthPrev FZ (AExprVariable (MkDeBruijnIdentifier FZ sourceId)) = ?oiueprqew --(AExprVariable (MkDeBruijnIdentifier FZ sourceId) ** ?erqwer)
exprDepthPrev (FS x) (AExprVariable (MkDeBruijnIdentifier FZ sourceId)) = ?exprDepthPrev_rhs_6
exprDepthPrev binderDepth (AExprVariable (MkDeBruijnIdentifier (FS x) sourceId)) = ?exprDepthPrev_rhs_4
exprDepthPrev binderDepth (AExprLambda x y) = ?exprDepthPrev_rhs_2
exprDepthPrev binderDepth (AExprDefApp x xs) = ?exprDepthPrev_rhs_5
exprDepthPrev binderDepth (AExprArrow x y) = ?exprDepthPrev_rhs_8


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


-- substituteTopBound {finalT} {bindType} (Var (Bound n)) withTerm bindIndex b_t@(VarBound elemPrf) r_t extra_len =
--     let same_t : (finalT = bindType) = ?eqewrqwe in
--     case same_t of
--     Refl =>
--         case decEq n bindIndex of
--         (Yes Refl) => (withTerm ** weakening r_t)
--         (No contra) => (Var (Bound n) ** ?eqweeeeer)
--
-- substituteTopBound (App left right) withTerm bindIndex (ApplRule left_t right_t) r_t extra_len =
--     let (outLeft ** outLeft_t) = substituteTopBound left withTerm bindIndex left_t r_t extra_len in
--     let (outRight ** outRight_t) = substituteTopBound right withTerm bindIndex right_t r_t extra_len in
--     (App outLeft outRight ** ApplRule outLeft_t outRight_t)
-- substituteTopBound {extraDecls} {gamma = gamma} {bindType = bindType} {finalT = (Arrow rho xi)} (Lambda rho body) withTerm bindIndex (AbstRule body_t) r_t extra_len =
--     let body_t' : Holds (MkTypeJudgment ((rho :: extraDecls) ++ (push bindType gamma)) body xi) = ?eqwerqwer in
--     let (newBody ** newBody_t) = substituteTopBound {extraDecls=rho :: extraDecls} body withTerm (S bindIndex) body_t' r_t (cong {f=S} extra_len) in
--     let newBody_t' : Holds (MkTypeJudgment (push rho (extraDecls ++ gamma)) newBody xi) = ?opueqwer in
--     (Lambda rho newBody ** AbstRule newBody_t')

mutual

    public export
    substituteTop : (idx : Nat) -> (LTE idx cd) -> (b : AExpr (ed, S cd)) -> (n : AExpr (ed, cd)) -> AExpr (ed, cd)
    substituteTop idx idx_lte AExprPostulate n = AExprPostulate
    substituteTop idx idx_lte AExprStar n = AExprStar
    substituteTop idx idx_lte AExprBox n = AExprBox
    substituteTop idx idx_lte (AExprApp l r) n = AExprApp (substituteTop idx idx_lte l n) (substituteTop idx idx_lte r n)
    substituteTop idx idx_lte (AExprDefApp x args) n = AExprDefApp x (substituteArgs idx idx_lte args n)
    substituteTop idx idx_lte (AExprLambda (MkADecl t src) body) n =
        let type' = substituteTop idx idx_lte t n in
        let body' = substituteTop (S idx) (LTESucc idx_lte) body (assert_smaller n (exprDepthS FZ n)) in
        AExprLambda (MkADecl type' src) body'
    substituteTop idx idx_lte (AExprArrow (MkADecl t src) body) n =
        let type' = substituteTop idx idx_lte t n in
        let body' = substituteTop (S idx) (LTESucc idx_lte) body (assert_smaller n (exprDepthS FZ n)) in
        AExprArrow (MkADecl type' src) body'
    substituteTop {ed} {cd} Z idx_lte (AExprVariable (MkDeBruijnIdentifier FZ src)) n = n
    substituteTop {ed} {cd = Z} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier FZ src)) n = absurd idx_lte
    substituteTop {ed} {cd = S cd} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier FZ src)) n = AExprVariable (MkDeBruijnIdentifier FZ src)
    substituteTop {ed} {cd} Z idx_lte (AExprVariable (MkDeBruijnIdentifier (FS x) src)) n = AExprVariable (MkDeBruijnIdentifier x src)
    substituteTop {ed} {cd = Z} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier (FS x) src)) n = absurd idx_lte
    substituteTop {ed} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier (FS x) src)) n =
        substituteTop k (lteSuccLeft idx_lte) (AExprVariable (MkDeBruijnIdentifier (weaken x) src)) n

    substituteTop idx idx_lte expr n = ?opiuwerwere

    public export
    substituteArgs : (idx : Nat) -> (LTE idx cd) -> List (AExpr (ed, S cd)) -> (n : AExpr (ed, cd)) -> List (AExpr (ed, cd))
    substituteArgs idx idx_lte [] n = []
    substituteArgs idx idx_lte (x :: xs) n = (substituteTop idx idx_lte x n) :: (substituteArgs idx idx_lte xs n)


public export
data Holds : TypeJudgment -> Type where
    -- HackHolds : Holds $ gamma |- (e1, t1) -> AlphaEquivalent e1 e2 -> AlphaEquivalent t1 t2 -> Holds $ gamma |- (e2, t2)
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
