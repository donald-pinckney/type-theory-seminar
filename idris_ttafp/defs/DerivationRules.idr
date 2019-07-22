module defs.DerivationRules

import defs.Judgments
import defs.AST


public export
data Holds : TypeJudgment -> Type where -- No derivation rules yet here! In other words, Holds J = Void
