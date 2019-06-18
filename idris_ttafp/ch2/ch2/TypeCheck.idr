module ch2.TypeCheck

import ch2.Judgments
import ch2.DerivationRules

checkTypeJudgment : (J : TypeJudgment) -> Dec (Holds J)
