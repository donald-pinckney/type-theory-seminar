module defs.BetaEquivalence

import defs.Identifier
import defs.BindingDepth
import Data.Fin
import Data.So
import Decidable.Order
import defs.AST
import defs.ResultDec
import defs.AlphaEquivalence

%default total

public export
deBruijnInc : DeBruijnIdentifier cd -> DeBruijnIdentifier (S cd)
deBruijnInc (MkDeBruijnIdentifier deBruijn sourceId) = MkDeBruijnIdentifier (FS deBruijn) sourceId

public export
deBruijnS : Fin (S cd) -> DeBruijnIdentifier cd -> DeBruijnIdentifier (S cd)
deBruijnS FZ (MkDeBruijnIdentifier deBruijn sourceId) = MkDeBruijnIdentifier (FS deBruijn) sourceId
deBruijnS (FS x) (MkDeBruijnIdentifier FZ sourceId) = MkDeBruijnIdentifier FZ sourceId
deBruijnS (FS binderDepth') (MkDeBruijnIdentifier (FS deBruijn') sourceId) =
    deBruijnInc $ deBruijnS binderDepth' (MkDeBruijnIdentifier deBruijn' sourceId)

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


-- predFin : Fin

public export
chooseNatOrder : (n : Nat) -> (m : Nat) -> Either (GT n m) (Either (n = m) (LT n m))
chooseNatOrder Z Z = Right (Left Refl)
chooseNatOrder Z (S k) = Right (Right (LTESucc LTEZero))
chooseNatOrder (S k) Z = Left (LTESucc LTEZero)
chooseNatOrder (S k) (S j) =
    let ih = chooseNatOrder k j in
    case ih of
        (Left l) => Left $ LTESucc l
        (Right (Left l)) => Right (Left (cong {f=S} l))
        (Right (Right r)) => Right (Right (LTESucc r))


public export
gt_not_zero : GT n m -> Not (n = Z)
gt_not_zero {n = (S right)} {m = m} (LTESucc x) = SIsNotZ


public export
strengthenFin : (x : Fin (S n)) -> LT (finToNat x) n -> Fin n
strengthenFin {n = Z} x lt_n = absurd lt_n
strengthenFin {n = (S k)} FZ lt_n = FZ
strengthenFin {n = (S k)} (FS x) lt_n = FS (strengthenFin x (fromLteSucc lt_n))

public export
finPred : (x : Fin (S n)) -> Not (finToNat x = Z) -> Fin n
finPred FZ not_z = void $ not_z Refl
finPred (FS x) not_z = x


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

    substituteTop {cd} idx idx_lte (AExprVariable (MkDeBruijnIdentifier x src)) n =
        case chooseNatOrder (finToNat x) idx of
            (Right (Left x_eq_idx)) => n
            (Left x_gt_idx) =>
                let x_not_z = gt_not_zero x_gt_idx in
                AExprVariable (MkDeBruijnIdentifier (finPred x x_not_z) src)
            (Right (Right x_lt_idx)) =>
                let x_lt_cd : Prelude.Nat.LT (finToNat x) cd = x_lt_idx `lteTransitive` idx_lte in
                AExprVariable (MkDeBruijnIdentifier (strengthenFin x x_lt_cd) src)


        -- if finToNat x > idx then -- idx < S cd,    finToNat x < S cd,   idx < finToNat x < S cd
        --     ?iuwerwer
        --     -- AExprVariable (MkDeBruijnIdentifier x-1 src)
        -- else if finToNat x < idx then -- idx < S cd, finToNat x < S cd, finToNat x < idx < S cd
        --     ?poiuwerqwer3
        --     -- AExprVariable (MkDeBruijnIdentifier x src)
        -- else
        --     n

    -- substituteTop {ed} {cd} Z idx_lte (AExprVariable (MkDeBruijnIdentifier FZ src)) n = n
    -- substituteTop {ed} {cd = Z} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier FZ src)) n = absurd idx_lte
    -- substituteTop {ed} {cd = S cd} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier FZ src)) n = AExprVariable (MkDeBruijnIdentifier FZ src)
    -- substituteTop {ed} {cd} Z idx_lte (AExprVariable (MkDeBruijnIdentifier (FS x) src)) n = AExprVariable (MkDeBruijnIdentifier (x) src)
    -- substituteTop {ed} {cd = Z} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier (FS x) src)) n = absurd idx_lte
    -- substituteTop {ed} (S k) idx_lte (AExprVariable (MkDeBruijnIdentifier (FS x) src)) n =
    --     let tmp = substituteTop k (lteSuccLeft idx_lte) (AExprVariable (MkDeBruijnIdentifier (weaken x) src)) n in
    --     tmp

    substituteTop idx idx_lte expr n = ?opiuwerwere

    public export
    substituteArgs : (idx : Nat) -> (LTE idx cd) -> List (AExpr (ed, S cd)) -> (n : AExpr (ed, cd)) -> List (AExpr (ed, cd))
    substituteArgs idx idx_lte [] n = []
    substituteArgs idx idx_lte (x :: xs) n = (substituteTop idx idx_lte x n) :: (substituteArgs idx idx_lte xs n)



public export
eval : AExpr (ed, cd) -> AExpr (ed, cd)
eval AExprPostulate = AExprPostulate
eval (AExprLambda (MkADecl x src) y) = AExprLambda (MkADecl (eval x) src) (eval y)
eval (AExprVariable x) = AExprVariable x
eval (AExprDefApp x xs) = ?eval_rhs_5
eval AExprStar = AExprStar
eval AExprBox = AExprBox
eval (AExprArrow (MkADecl x src) y) = AExprArrow (MkADecl (eval x) src) (eval y)
eval (AExprApp x y) = AExprApp (eval x) (eval y)
eval (AExprApp (AExprLambda (MkADecl type src) body) arg) = substituteTop Z LTEZero body arg



public export
data BetaEquivalent : AExpr d -> AExpr d -> Type where
    AlphaRefl : AlphaEquivalent a b -> BetaEquivalent a b
    Normalized : AlphaEquivalent (eval a) (eval b) -> BetaEquivalent a b

-- alphaImpliesBeta : (a : AExpr (ed, cd)) -> (b : AExpr (ed, cd)) -> AlphaEquivalent a b -> BetaEquivalent a b
-- alphaImpliesBeta AExprPostulate AExprPostulate AlphaEquivalentPostulate = ?alphaImpliesBeta_rhs_1
-- alphaImpliesBeta AExprStar AExprStar AlphaEquivalentStar = ?alphaImpliesBeta_rhs_2
-- alphaImpliesBeta AExprBox AExprBox AlphaEquivalentBox = Normalized AlphaEquivalentBox
-- alphaImpliesBeta (AExprVariable (MkDeBruijnIdentifier x src1)) (AExprVariable (MkDeBruijnIdentifier x src2)) AlphaEquivalentVariable = ?alphaImpliesBeta_rhs_4
-- alphaImpliesBeta (AExprLambda (MkADecl t1 src1) m1) (AExprLambda (MkADecl t2 src2) m2) (AlphaEquivalentLambda x y) = ?alphaImpliesBeta_rhs_5
-- alphaImpliesBeta (AExprArrow (MkADecl t1 src1) m1) (AExprArrow (MkADecl t2 src2) m2) (AlphaEquivalentArrow x y) = ?alphaImpliesBeta_rhs_6
-- alphaImpliesBeta (AExprDefApp (MkDeBruijnIdentifier x src1) args1) (AExprDefApp (MkDeBruijnIdentifier x src2) args2) (AlphaEquivalentDefApp y) = ?alphaImpliesBeta_rhs_7
-- alphaImpliesBeta (AExprApp l1 r1) (AExprApp l2 r2) (AlphaEquivalentApp l1l2 r1r2) = Normalized ?pouwerwer

export
isBetaEquivalent : (a : AExpr (ed, cd)) -> (b : AExpr (ed, cd)) -> ResultDec (BetaEquivalent a b)
isBetaEquivalent a b =
    case isAlphaEquivalent (eval a) (eval b) of
        (Ok prf) => Ok $ Normalized prf
        (Error msg f) => Error ("not beta equivalent:\n\t" ++ show a ++ "\nExpected:\n\t" ++ show b) ?oipuwerqwer
