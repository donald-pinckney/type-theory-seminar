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

-- Consequently, we reject all programs
type_check : (j : TypeJudgment) -> Dec (Holds j)
type_check (MkTypeJudgment {cd} context AExprStar AExprBox) =
    case context of
        [] => Yes SortHolds
        (x :: y) => ?sort_rule_use_weaken -- need to use weakening here

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

        FS x => ?var_rule_use_weaken -- We need to use weakening here


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
