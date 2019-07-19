module defs.Judgments

import defs.AST

public export
record TypeJudgment where
    constructor MkTypeJudgment
    -- env : ???
    -- context : ???
    term : AExpr n m
    type : AExpr n m
