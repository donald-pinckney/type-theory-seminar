module ch2.Judgments

import ch2.Context
import ch2.AST

%default total

public export
record TypeJudgment where
    constructor MkTypeJudgment
    context : Context
    term : Term
    type : Type'
