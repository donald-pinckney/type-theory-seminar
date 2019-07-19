module defs.TypeCheck

import defs.AST
import defs.DerivationRules
import defs.Judgments
import defs.Identifier
import Result

%default total

-- There are no derivation rules, so any judgment holding is a contradiction
Uninhabited (Holds j) where

-- Consequently, we reject all programs
type_check : (j : TypeJudgment) -> Dec (Holds j)
type_check j = No absurd


export
type_check_main : ABook n m -> Result ()
type_check_main ABookNil = success ()
type_check_main (ABookConsSuppose x y) = error "Suppose checking is not implemented!"
type_check_main (ABookConsDef (MkADef body type sourceId sourceArgs) rest_book) =
    let j = MkTypeJudgment body type in
    case type_check j of
        (Yes prf) => type_check_main rest_book
        (No contra) => error "Failed to type check: "
