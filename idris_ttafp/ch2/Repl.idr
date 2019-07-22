module ch2.Repl

import Shared.AbstractRepl
import Shared.Result
import ch2.AST
import ch2.BetaNormalForm
import ch2.BetaReduction
import ch2.PrettyPrint
import ch2.Resolve
import ch2.Context
import ch2.DerivationRules
import ch2.Judgments
import ch2.TypeCheck
import ch2.LatexPrinting
import Shared.ParseUtils


ReplState : Type
ReplState = ()

Command_isBNF : Term -> ReplCommand ReplState
Command_isBNF term state = pure $ success $ Just (show $ decAsBool $ isInBNF term, state)

Command_multiStep : Term -> ReplCommand ReplState
-- Command_multiStep term state =
--     let (newTerm ** bnf) = betaMultiStep ?eqwerwer term in
--     success $ Just (prettyPrintTerm newTerm, state)

Command_singleStep : Term -> ReplCommand ReplState
-- Command_singleStep term state = case betaSingleStep term of
--     (Left newTerm) => success $ Just (prettyPrintTerm newTerm, state)
--     (Right bnf) => success $ Just ("Term already in BNF", state)

-- findType : (gamma : Context) -> (term : Term) -> Dec (sigma : Type' ** Holds $ MkTypeJudgment gamma term sigma)

Command_typeFind : Term -> ReplCommand ReplState
Command_typeFind term state =
    let emptyContext = MkContext ([] ** NilValid) [] in
    case findType emptyContext term of
        (Yes prf) => pure $ success $ Just (prettyPrintType $ fst prf, state)
        (No contra) => pure $ error "type check failed"

Command_typeFindPrf : Term -> ReplCommand ReplState
Command_typeFindPrf term state =
    let emptyContext = MkContext ([] ** NilValid) [] in
    case findType emptyContext term of
        (Yes prf) => do
            writeLatexFile "prf" (snd prf)
            pure $ success $ Just (prettyPrintType $ fst prf, state)
        (No contra) => pure $ error "type check failed"

    -- let emptyContext = MkContext ([] ** NilValid) [] in
    -- case findType emptyContext term of
    --     (Yes prf) => success $ Just (prettyPrintType $ fst prf, state)
    --     (No contra) => error "type check failed"

-- total
SupportedCommands : List (CommandBuilder ReplState)
SupportedCommands = [
    MkCommandBuilder [['t'],['t','y','p','e']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_typeFind)) "<term>" "Finds the type of <term>.",
    MkCommandBuilder [['p']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_typeFindPrf)) "<term>" "Finds the type of <term>.",
    MkCommandBuilder [['e'],['e','v','a','l']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_multiStep)) "<term>" "Performs beta multistep on <term> until it is in BNF.",
    MkCommandBuilder [['i','s','B','N','F']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_isBNF)) "<term>" "Tests if <term> is in BNF, and gives a proof.",
    MkCommandBuilder [['s','t','e','p']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_singleStep)) "<term>" "Performs one step of beta reduction on <term>."
]


export
replCh2 : IO ()
replCh2 = replMain SupportedCommands (believe_me ()) ()
