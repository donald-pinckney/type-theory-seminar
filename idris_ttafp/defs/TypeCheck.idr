module defs.TypeCheck

import defs.AST
import defs.DerivationRules
import defs.Identifier
import defs.BindingDepth
import defs.AlphaEquivalence
import Shared.Result
import Shared.ParseUtils
import Decidable.Order
import defs.ResultDec
import defs.BetaEquivalence

import Data.So
import Data.Fin

import Debug.Error
import Debug.Trace
%language ElabReflection

%default total


mutual
    check_sort : (n : Nat) -> (context : Context ed cd) -> (e : AExpr (ed, cd)) -> ResultDec (t : AExpr (ed, cd) ** (Holds $ context |- (e, t), IsSort t))
    check_sort n context e = case find_type_log (S n) context e of
        (Ok (t ** prf)) => case isSort t of
            (Ok t_sort) => Ok (t ** (prf, t_sort))
            (Error msg not_sort) => Error ((show t) ++ " is not a sort.") ?check_sort_not_sort
        (Error msg contra) => Error msg ?check_sort_no_type


    try_alpha_beta_conv : (n : Nat) -> Holds $ context |- (a, b) -> (b' : AExpr (ed, cd)) -> ResultDec $ Holds $ context |- (a, b')
    try_alpha_beta_conv {context} {b} n ab b' = case isAlphaEquivalent b b' of
        (Ok eq_types) => Ok $ AlphaHolds ab eq_types
        (Error msg not_alpha) => case isBetaEquivalent b b' of
            (Ok bb') => case check_sort (S n) context b' of
                (Ok (bt' ** (prf, prf_sort))) => Ok $ ConvHolds {isSort=prf_sort} ab prf bb'
                (Error msg not_sort') => Error msg ?opiuwerme
            (Error msg_not_beta not_beta) => Error msg_not_beta ?ouiwerqwer


    use_weaken : (n : Nat) -> (Holds $ context |- (a, b)) -> ResultDec $ Holds $ (c :: context) |- (exprDepthS FZ a, exprDepthS FZ b)
    use_weaken {context} {c} n a_b =
        case assert_total (check_sort (S n) context c) of
            (Ok (ct ** (ct_prf, prf_sort))) => Ok $ WeakHolds {isSort=prf_sort} a_b ct_prf
            (Error x f) => Error ?opuwerwereee ?oiuwer_3 -- Definitely a type check error

    use_weaken_find : (n : Nat) -> (b : AExpr (ed, cd) ** Holds $ context |- (a, b)) -> ResultDec (t : AExpr (ed, S cd) ** Holds $ (c :: context) |- (exprDepthS FZ a, t))
    use_weaken_find {c} {cd} {ed} {context} n (b ** prf) = case use_weaken (S n) {c=c} prf of
        (Ok weak_prf) => Ok (exprDepthS FZ b ** weak_prf)
        (Error msg contra) => ?oiuwerwer_2 -- Definitely a type check error


    find_type_log : (n : Nat) -> (context : Context ed cd) -> (e : AExpr (ed, cd)) -> ResultDec (t : AExpr (ed, cd) ** Holds $ context |- (e, t))
    find_type_log n context e =
        -- trace (concat (replicate n "  ") ++ "trying to find: " ++ (show context) ++ " |- " ++ (show e)) $
        find_type n context e



    find_type : (n : Nat) -> (context : Context ed cd) -> (e : AExpr (ed, cd)) -> ResultDec (t : AExpr (ed, cd) ** Holds $ context |- (e, t))
    find_type {cd = Z} {ed} n [] AExprStar = Ok (AExprBox ** SortHolds)
    find_type {cd = S cd} {ed} n (t :: ts) AExprStar = case assert_total (find_type_log (S n) ts AExprStar) of
        (Ok t_prf) => use_weaken_find (S n) t_prf
        (Error msg contra) => ?opiuwerw_2 -- Definitely a type check error

    find_type {cd = Z} {ed} n [] (AExprVariable (MkDeBruijnIdentifier deBruijn src)) = absurd deBruijn
    find_type {cd = S cd} {ed} n (ct :: cts) (AExprVariable (MkDeBruijnIdentifier deBruijn src)) =
        case deBruijn of
            FZ => case assert_total (check_sort (S n) cts ct) of
                        Ok (ct_t ** (ct_prf, ct_sort)) =>
                            Ok (exprDepthS FZ ct ** VarHolds {src=src} {isSort=ct_sort} cts ct ct_prf)
                        -- This is definitely a type check error, since the given 'type' is not a type or kind
                        Error msg1 c1 => ?asdfdfd_3

            FS x => -- We need to use weakening here
                case assert_total (find_type_log (S n) cts (AExprVariable (MkDeBruijnIdentifier x src))) of
                    (Ok t_prf) => use_weaken_find (S n) t_prf
                    (Error msg contra) => ?var_rule_use_weaken_2 -- This is definitely a type check error

    find_type {cd} {ed} n context (AExprArrow (MkADecl a x_src) b) =
        case assert_total (check_sort (S n) context a, check_sort (S n) (a :: context) b) of
            (Ok (s1 ** (s1_prf, sort1)), Ok (AExprStar ** (s2_prf, SortStar))) =>
                Ok (AExprStar ** FormHolds {isSort1 = sort1} {isSort2 = SortStar} context a b s1_prf s2_prf)
            (Ok (s1 ** (s1_prf, sort1)), Ok (AExprBox ** (s2_prf, SortBox))) =>
                Ok (AExprBox ** FormHolds {isSort1 = sort1} {isSort2 = SortBox} context a b s1_prf s2_prf)
            (Error msg1 s1_contra, _) => ?arrow_invalid_bind_type -- Definitely a type error
            (_, Error msg2 s2_contra) => ?arrow_invalid_result_type -- Definitely a type error

    find_type {cd} {ed} n context (AExprLambda (MkADecl a src_a) m) =
        case assert_total (find_type_log (S n) (a :: context) m) of
            (Ok (b ** m_b_prf)) => case assert_total (check_sort (S n) context (AExprArrow (MkADecl a src_a) b)) of
                (Ok (s ** (s_prf, s_sort))) =>
                    Ok (AExprArrow (MkADecl a src_a) b ** AbstHolds {isSort=s_sort} m_b_prf s_prf)
                (Error msg pi_contra) => ?find_type_log_lambda_pi_bad -- Type error?
            (Error msg b_contra) => ?find_type_log_lambda_body_bad -- Definitely a type error since body can't type check


    find_type {cd} {ed} n context (AExprApp f arg) = case (find_type_log (S n) context f) of
        Ok (AExprArrow (MkADecl a src) b ** arrow_prf) => case assert_total (type_check (S n) $ context |- (arg, a)) of
            (Ok arg_prf) => Ok (substituteTop Z LTEZero b arg ** ApplHolds {src=src} arrow_prf arg_prf)
            (Error arg_msg arg_contra) => ?oiuwerwer_4
        Ok (ft ** ft_prf) => ?pouwereee_4
        Error f_msg f_contra => ?pouwereee_2

    find_type n context AExprBox = Error "box is not a sort" ?no_box_prf
    find_type n context e = error ("find_type_log missing case: " ++ (show context) ++ " |- " ++ (show e)) --?find_type_log_other_cases


    type_check : (n : Nat) -> (j : TypeJudgment) -> ResultDec (Holds j)
    -- type_check (MkTypeJudgment {cd=Z} {ed} [] AExprStar AExprBox) = Ok SortHolds
    -- type_check (MkTypeJudgment {cd=S cd} {ed} (t :: ts) AExprStar AExprBox) =
    --     case assert_total (type_check $ ts |- (AExprStar, AExprBox)) of
    --         (Ok prf) => use_weaken prf
    --         (Error msg contra) => Error ?opuwerweq ?erqwer_2 -- Definitely a type error
    --
    -- type_check (MkTypeJudgment {cd=Z} {ed} [] (AExprVariable (MkDeBruijnIdentifier deBruijn src)) type) = absurd deBruijn
    -- type_check (MkTypeJudgment {cd=S cd} {ed} (t :: ts) (AExprVariable (MkDeBruijnIdentifier deBruijn src)) type) =
    --     case deBruijn of
    --         FZ => case isAlphaEquivalent (exprDepthS FZ t) type of
    --             Ok t_eq_type => case assert_total (type_check (ts |- (t, AExprStar)), type_check (ts |- (t, AExprBox))) of
    --                 (Ok prf, _) =>
    --                     let vh = VarHolds {src=src} {isSort=SortStar} ts t prf in
    --                     use_conv vh (AlphaRefl t_eq_type)
    --                 (_, Ok prf) =>
    --                     let vh = VarHolds {src=src} {isSort=SortBox} ts t prf in
    --                     use_conv vh (AlphaRefl t_eq_type)
    --
    --                 -- This is definitely a type check error, since the given 'type' is not a type or kind
    --                 (Error msg1 c1, Error msg2 c2) => Error ?jouy2qwer ?asdfdfd_3
    --
    --             (Error msg t_neq_type) => Error ?themsg ?oiwerwer_2 -- This is definitely a type check error since the types don't match
    --
    --         FS x => -- We need to use weakening here
    --             case find_type_log ts (AExprVariable (MkDeBruijnIdentifier x src)) of
    --             (Ok (type' ** prf)) => case use_weaken {c=t} prf of
    --                  (Ok prf_weak) => case isAlphaEquivalent (exprDepthS FZ type') type of
    --                      (Ok eq_types) =>
    --                         use_conv prf_weak (AlphaRefl eq_types)
    --                      (Error msg r) => ?opuiwewer_2
    --                  (Error msg contra) => ?var_rule_use_weaken_4 -- this is definitely a type error
    --             (Error msg contra) => ?var_rule_use_weaken_2 -- This is definitely a type check error
    --
    --
    -- type_check (MkTypeJudgment context (AExprArrow (MkADecl a x_src) b) s2) =
    --     case (isSort s2, assert_total (
    --             type_check $ context |- (a, AExprStar),
    --             type_check $ context |- (a, AExprBox),
    --             type_check $ (a :: context) |- (b, exprDepthS FZ s2))) of
    --         (Error msg_s2 s2_notSort, _, _, _) => ?opuewrwer -- Definitely a type error
    --         (_, _, _, Error msg_b b_not_s2) => ?opuiwerwer -- Definitely a type error
    --         (Ok s2_sort, Ok a_star, _tc_box, Ok b_s2) =>
    --             Ok $ FormHolds {isSort1=SortStar} {isSort2=s2_sort} context a b a_star b_s2
    --         (Ok s2_sort, _tc_star, Ok a_box, Ok b_s2) =>
    --             Ok $ FormHolds {isSort1=SortBox} {isSort2=s2_sort} context a b a_box b_s2
    --         (_, Error msg1 c1, Error msg2 c2, _) => ?poiuwerqwer -- Definitely a type error
    --
    --
    -- type_check (MkTypeJudgment {cd} {ed} context (AExprLambda (MkADecl a x_src) m) t) =
    --     case find_type_log context (AExprLambda (MkADecl a x_src) m) of
    --         (Ok (t' ** t_prf')) => case isAlphaEquivalent t' t of
    --             (Ok eq_types) =>
    --                 use_conv t_prf' (AlphaRefl eq_types)
    --             (Error msg different_types) => ?poiuwerwer_2 -- Definitely a type error
    --
    --         (Error msg contra) => ?oiuwerwer_3 -- Definitely a type error

    type_check n j@(MkTypeJudgment {cd} {ed} context a t) =
        -- trace (concat (replicate n "  ") ++ "trying to check: " ++ (show j)) $ -- Ok ?pouiwerqwer
        case find_type_log (S n) context a of
            (Ok (t' ** prf')) => try_alpha_beta_conv (S n) prf' t
            (Error msg contra) => Error msg ?no_type_prf



export
type_check_main : ABook (ed, Z) -> Result ()
type_check_main ABookNil = success ()
type_check_main (ABookConsSuppose x y) = error "Suppose checking is not implemented!"
type_check_main (ABookConsDef (MkADef body type sourceId sourceArgs) rest_book) =
    let j = MkTypeJudgment [] body type in
    case type_check Z j of
        (Ok prf) => type_check_main rest_book
        (Error msg contra) => error $ "Failed to type check: " ++ msg
