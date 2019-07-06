module defs.Repl

import AbstractRepl
import Result
import defs.AST
-- import ch2.BetaNormalForm
-- import ch2.BetaReduction
import defs.PrettyPrint
import defs.Resolve
-- import ch2.Context

-- ReplState : Type
-- ReplState = ()
--
-- Command_isBNF : Term -> ReplCommand ReplState
-- Command_isBNF term state = success $ Just (show $ decAsBool $ isInBNF term, state)
--
-- Command_multiStep : Term -> ReplCommand ReplState
-- -- Command_multiStep term state =
-- --     let (newTerm ** bnf) = betaMultiStep term in
-- --     success $ Just (prettyPrintTerm newTerm, state)
--
-- Command_singleStep : Term -> ReplCommand ReplState
-- -- Command_singleStep term state = case betaSingleStep term of
-- --     (Left newTerm) => success $ Just (prettyPrintTerm newTerm, state)
-- --     (Right bnf) => success $ Just ("Term already in BNF", state)
--
--
-- -- total
-- SupportedCommands : List (CommandBuilder ReplState)
-- SupportedCommands = [
--     MkCommandBuilder [['e'],['e','v','a','l']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_multiStep)) "<term>" "Performs beta multistep on <term> until it is in BNF.",
--     MkCommandBuilder [['i','s','B','N','F']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_isBNF)) "<term>" "Tests if <term> is in BNF, and gives a proof.",
--     MkCommandBuilder [['s','t','e','p']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_singleStep)) "<term>" "Performs one step of beta reduction on <term>."
-- ]
--
--
-- export
-- replCh2 : IO ()
-- replCh2 = replMain SupportedCommands (believe_me ()) ()
