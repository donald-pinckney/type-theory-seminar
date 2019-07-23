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
        (x :: y) => ?tc_rhs1_2

type_check (MkTypeJudgment {cd=Z} {ed} [] (AExprVariable (MkDeBruijnIdentifier deBruijn src)) type) = absurd deBruijn
type_check (MkTypeJudgment {cd=S cd} {ed} (t :: ts) (AExprVariable (MkDeBruijnIdentifier deBruijn src)) type) =
    case deBruijn of
        FZ => case choose (exprDepthS FZ t == type) of
            Left t_eq_type => case assert_total (type_check (ts |- (t, AExprStar)), type_check (ts |- (t, AExprBox))) of
                (Yes prf, _) =>
                     let vh = VarHolds {src=src} {s = AExprStar} ts t prf in
                     Yes $ HackHolds vh Oh t_eq_type
                (_, Yes prf) =>
                    let vh = VarHolds {src=src} {s = AExprBox} ts t prf in
                    Yes $ HackHolds vh Oh t_eq_type

                -- This is definitely a type check error, since the given 'type' is not a type or kind
                (No c1, No c2) => ?asdfdfd_3

            Right t_neq_type => ?oiwerwer_2 -- This is definitely a type check error since the types don't match

        FS x => ?asdfadsfaf_3 -- We need to use weakening here

type_check _ = No absurd


export
type_check_main : ABook (ed, Z) -> Result ()
type_check_main ABookNil = success ()
type_check_main (ABookConsSuppose x y) = error "Suppose checking is not implemented!"
type_check_main (ABookConsDef (MkADef body type sourceId sourceArgs) rest_book) =
    let j = MkTypeJudgment [] body type in
    case type_check j of
        (Yes prf) => type_check_main rest_book
        (No contra) => error "Failed to type check: "
