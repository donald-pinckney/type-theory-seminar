module defs.Judgments

import defs.AST
import defs.Environments

public export
record TypeJudgment where
    constructor MkTypeJudgment
    -- env : ???
    -- context : ???
    term : AExpr depth
    type : AExpr depth
