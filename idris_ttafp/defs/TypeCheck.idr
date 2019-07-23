module defs.TypeCheck

import defs.AST
import defs.DerivationRules
import defs.Identifier
import defs.BindingDepth
import Shared.Result
import Shared.ParseUtils

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
type_check (MkTypeJudgment {cd} context (AExprVariable x) type) = 
  case context of
        [] => No ?rhs_we_fucked
        t :: ts => (case x of
            MkDeBruijnIdentifier deBruijn src => (case deBruijn of
                FZ => if exprDepthS FZ t == type
                        then assert_total (case (type_check (ts |- (t, AExprStar)), type_check (ts |- (t, AExprBox))) of
                            (Yes prf, _)   => 
                                             let vh = VarHolds {s = AExprStar} ts t ?eqewqwre in
                                             Yes $ ?wewewer
                            (_, Yes prf)   => ?asdfdsfdf_2
                            (No c1, No c2) => ?asdfdfd_3
                            ) 
                        else ?adsfd
                FS x => ?asdfadsfaf_3))
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
