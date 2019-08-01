module defs.TypeCheck

import defs.AST
import defs.DerivationRules
import defs.Identifier
import defs.BindingDepth
import Shared.Result
import Shared.ParseUtils

import Data.So
import Data.Fin

%default total


-- There are no derivation rules, so any judgment holding is a contradiction
Uninhabited (Holds j) where


fin_eq : (x : Fin b) -> So (x == x)
fin_eq FZ = Oh
fin_eq (FS x) = fin_eq x

mutual
    use_weaken : (Holds $ context |- (a, b)) -> Dec $ Holds $ (c :: context) |- (exprDepthS FZ a, exprDepthS FZ b)
    use_weaken {context} {c} a_b = case assert_total (type_check $ context |- (c, AExprStar), type_check $ context |- (c, AExprBox)) of
        (Yes c_star, _box_tc) => Yes $ WeakHolds {isSort=SortStar} a_b c_star
        (_star_tc, Yes c_box) => Yes $ WeakHolds {isSort=SortBox} a_b c_box
        (No c1, No c2) => No ?oiuwer_3 -- Definitely a type check error

    use_weaken_find : (b : AExpr (ed, cd) ** Holds $ context |- (a, b)) -> Dec (t : AExpr (ed, S cd) ** Holds $ (c :: context) |- (exprDepthS FZ a, t))
    use_weaken_find {c} {cd} {ed} {context} (b ** prf) = case use_weaken {c=c} prf of
        (Yes weak_prf) => Yes (exprDepthS FZ b ** weak_prf)
        (No contra) => ?oiuwerwer_2 -- Definitely a type check error


    find_type : (context : Context ed cd) -> (e : AExpr (ed, cd)) -> Dec (t : AExpr (ed, cd) ** Holds $ context |- (e, t))
    find_type {cd = Z} {ed} [] AExprStar = Yes (AExprBox ** SortHolds)
    find_type {cd = S cd} {ed} (t :: ts) AExprStar = case find_type ts AExprStar of
        (Yes t_prf) => use_weaken_find t_prf
        (No contra) => ?opiuwerw_2 -- Definitely a type check error

    find_type {cd = Z} {ed} [] (AExprVariable (MkDeBruijnIdentifier deBruijn src)) = absurd deBruijn
    find_type {cd = S cd} {ed} (ct :: cts) (AExprVariable (MkDeBruijnIdentifier deBruijn src)) =
        case deBruijn of
            FZ => case assert_total (type_check (cts |- (ct, AExprStar)), type_check (cts |- (ct, AExprBox))) of
                        (Yes prf, _) => Yes (exprDepthS FZ ct ** VarHolds {src=src} {isSort=SortStar} cts ct prf)
                        (_, Yes prf) => Yes (exprDepthS FZ ct ** VarHolds {src=src} {isSort=SortBox} cts ct prf)
                        -- This is definitely a type check error, since the given 'type' is not a type or kind
                        (No c1, No c2) => No ?asdfdfd_3

            FS x => -- We need to use weakening here
                case find_type cts (AExprVariable (MkDeBruijnIdentifier x src)) of
                    (Yes t_prf) => use_weaken_find t_prf
                    (No contra) => ?var_rule_use_weaken_2 -- This is definitely a type check error

    find_type {cd = cd} {ed = ed} context (AExprArrow (MkADecl a x_src) b) =
        case (find_type context a, find_type (a :: context) b) of
            (Yes (s1 ** s1_prf), Yes (s2 ** s2_prf)) => case (isSort s1, isSort s2) of
                (Yes s1_sort, Yes SortStar) => Yes (AExprStar ** FormHolds {isSort1 = s1_sort} {isSort2 = SortStar} context a b s1_prf s2_prf)
                (Yes s1_sort, Yes SortBox) => Yes (AExprBox ** FormHolds {isSort1 = s1_sort} {isSort2 = SortBox} context a b s1_prf s2_prf)

                (No s1_not_sort, _) => ?arrow_not_sort_bind -- Definitely a type error
                (_, No s2_not_sort) => ?arrow_not_sort_result -- Definitely a type error

            (No s1_contra, _) => ?arrow_invalid_bind_type -- Definitely a type error
            (_, No s2_contra) => ?arrow_invalid_result_type -- Definitely a type error


    find_type {cd} {ed} context (AExprLambda (MkADecl a src_a) m) =
        case find_type (a :: context) m of
            (Yes (b ** m_b_prf)) => case find_type context (AExprArrow (MkADecl a src_a) b) of
                (Yes (s ** s_prf)) => case isSort s of
                    (Yes s_sort) => Yes (AExprArrow (MkADecl a src_a) b ** AbstHolds {isSort=s_sort} m_b_prf s_prf)
                    (No s_not_sort) => ?find_type_lambda_pi_not_sort -- Type error?
                (No pi_contra) => ?find_type_lambda_pi_bad -- Type error?
            (No b_contra) => ?find_type_lambda_body_bad -- Definitely a type error since body can't type check

    find_type context _ = ?find_type_other_cases

    -- find_type {cd} {ed} context (AExprApp m n) = ?find_type_rhs_4
    -- find_type {cd = cd} {ed = ed} context (AExprDefApp x xs) = ?find_type_rhs_5
    -- find_type {cd = cd} {ed = ed} context AExprBox = ?find_type_rhs_7


    type_check : (j : TypeJudgment) -> Dec (Holds j)
    type_check (MkTypeJudgment {cd=Z} {ed} [] AExprStar AExprBox) = Yes SortHolds
    type_check (MkTypeJudgment {cd=S cd} {ed} (t :: ts) AExprStar AExprBox) =
        case assert_total (type_check $ ts |- (AExprStar, AExprBox)) of
            (Yes prf) => use_weaken prf
            (No contra) => No ?erqwer_2 -- Definitely a type error

    type_check (MkTypeJudgment {cd=Z} {ed} [] (AExprVariable (MkDeBruijnIdentifier deBruijn src)) type) = absurd deBruijn
    type_check (MkTypeJudgment {cd=S cd} {ed} (t :: ts) (AExprVariable (MkDeBruijnIdentifier deBruijn src)) type) =
        case deBruijn of
            FZ => case choose (exprDepthS FZ t == type) of
                Left t_eq_type => case assert_total (type_check (ts |- (t, AExprStar)), type_check (ts |- (t, AExprBox))) of
                    (Yes prf, _) =>
                         let vh = VarHolds {src=src} {isSort=SortStar} ts t prf in
                         Yes $ HackHolds vh Oh t_eq_type
                    (_, Yes prf) =>
                        let vh = VarHolds {src=src} {isSort=SortBox} ts t prf in
                        Yes $ HackHolds vh Oh t_eq_type

                    -- This is definitely a type check error, since the given 'type' is not a type or kind
                    (No c1, No c2) => No ?asdfdfd_3

                Right t_neq_type => No ?oiwerwer_2 -- This is definitely a type check error since the types don't match

            FS x => -- We need to use weakening here
                case find_type ts (AExprVariable (MkDeBruijnIdentifier x src)) of
                (Yes (type' ** prf)) => case use_weaken {c=t} prf of
                     (Yes prf_weak) => case choose (exprDepthS FZ type' == type) of
                         (Left eq_types) => Yes $ HackHolds prf_weak (fin_eq x) eq_types
                         (Right r) => ?opuiwewer_2
                     (No contra) => ?var_rule_use_weaken_4 -- this is definitely a type error
                (No contra) => ?var_rule_use_weaken_2 -- This is definitely a type check error


    type_check (MkTypeJudgment context (AExprArrow (MkADecl a x_src) b) s2) =
        case (isSort s2, assert_total (
                type_check $ context |- (a, AExprStar),
                type_check $ context |- (a, AExprBox),
                type_check $ (a :: context) |- (b, exprDepthS FZ s2))) of
            (No s2_notSort, _, _, _) => No ?opuewrwer -- Definitely a type error
            (_, _, _, No b_not_s2) => No ?opuiwerwer -- Definitely a type error
            (Yes s2_sort, Yes a_star, _tc_box, Yes b_s2) =>
                Yes $ FormHolds {isSort1=SortStar} {isSort2=s2_sort} context a b a_star b_s2
            (Yes s2_sort, _tc_star, Yes a_box, Yes b_s2) =>
                Yes $ FormHolds {isSort1=SortBox} {isSort2=s2_sort} context a b a_box b_s2
            (_, No c1, No c2, _) => No ?poiuwerqwer -- Definitely a type error


    type_check _ = No absurd

--No absurd


export
type_check_main : ABook (ed, Z) -> Result ()
type_check_main ABookNil = success ()
type_check_main (ABookConsSuppose x y) = error "Suppose checking is not implemented!"
type_check_main (ABookConsDef (MkADef body type sourceId sourceArgs) rest_book) =
    let j = MkTypeJudgment [] body type in
    case type_check j of
        (Yes prf) => type_check_main rest_book
        (No contra) => error "Failed to type check: "
