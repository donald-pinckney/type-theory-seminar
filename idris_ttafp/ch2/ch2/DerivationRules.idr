module ch2.DerivationRules

import ch2.Context
import ch2.Judgments
import ch2.AST
import ElemIdx

export
data Holds : TypeJudgment -> Type where
    VarBound : ElemIdx sigma (boundDecls gamma) n ->
        Holds $ MkTypeJudgment gamma (Var (Bound n)) sigma
    VarFree : ValueAtKey sigma (freeDecls gamma) v ->
        Holds $ MkTypeJudgment gamma (Var (Free v)) sigma
    ApplRule : Holds $ MkTypeJudgment gamma m (Arrow sigma tau) ->
        Holds $ MkTypeJudgment gamma n sigma ->
        Holds $ MkTypeJudgment gamma (App m n) tau
    AbstRule : Holds $ MkTypeJudgment (push sigma gamma) m tau ->
        Holds $ MkTypeJudgment gamma (Lambda sigma m) (Arrow sigma tau)
