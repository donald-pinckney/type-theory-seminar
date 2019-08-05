module defs.BetaEquivalence

import defs.Identifier
import defs.BindingDepth
import Data.Fin
import Data.So
import Decidable.Order
import defs.AST
import defs.ResultDec
import defs.AlphaEquivalence

public export
data BetaEquivalent : AExpr d -> AExpr d -> Type where
    AlphaRefl : AlphaEquivalent a b -> BetaEquivalent a b



export
isBetaEquivalent : (a : AExpr d) -> (b : AExpr d) -> ResultDec (BetaEquivalent a b)
