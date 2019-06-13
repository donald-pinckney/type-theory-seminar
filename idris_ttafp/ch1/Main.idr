module Main

import AST
import Resolve
import BetaNormalForm
import BetaReduction
import ParseUtils
import Result
import PrettyPrint

data ReplCommand =
      IsBNF Term
    | MultiStep Term
    | SingleStep Term
    | Help
    | Nop
    | Quit

ReplState : Type
ReplState = ()

-- isBNF_cmd : List Char
-- isBNF_cmd = ['i','s','B','N','F']
--
-- betaMultiStep_cmd : List Char

record CommandBuilder where
    constructor MkCommandBuilder
    commandStrs : List (List Char)
    buildFn : List Char -> Result ReplCommand
    argStrs : String
    docStrs : String


supportedCommands : List CommandBuilder
supportedCommands = [
    MkCommandBuilder [['i','s','B','N','F']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . IsBNF)) "<term>" "Tests if <term> is in BNF, and gives a proof.",
    MkCommandBuilder [['s','t','e','p']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . SingleStep)) "<term>" "Performs one step of beta reduction on <term>.",
    MkCommandBuilder [['e'],['e','v','a','l']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . MultiStep)) "<term>" "Performs beta multistep on <term> until it is in BNF.",
    MkCommandBuilder [['?'],['h'],['h','e','l','p']] (\rest => pure Help) "" "Display this help text.",
    MkCommandBuilder [['q'],['q','u','i','t']] (\rest => pure Quit) "" "Quits."
]

helpRow : CommandBuilder -> String
helpRow (MkCommandBuilder commandStrs buildFn argStrs docStrs) =
    let commandsStr = unwords $ map (\cmdStr => ":" ++ pack cmdStr) commandStrs in
    commandsStr ++ " " ++ argStrs ++ "\r\n\t" ++ docStrs

helpStr : String
helpStr = unlines $ map helpRow supportedCommands



buildCommand : List Char -> List Char -> Result ReplCommand
buildCommand cmd rest =
    case find (\b => any (==cmd) (commandStrs b)) supportedCommands of
        Nothing => error $ "Unrecognized command: :" ++ (pack cmd) ++ ". Type :help to see a list of supported commands."
        (Just b) => (buildFn b) rest


joinBy : List (List a) -> a -> List a
joinBy [] s = []
joinBy [xs] s = xs
joinBy (x :: xs) s = x ++ s :: (joinBy xs s)

firstWordSplit : List Char -> Result (List Char, List Char)
firstWordSplit xs =
    let words = split (== ' ') xs in
    case words of
        [] => error "Expected word"
        (w :: ws) => success (w, joinBy ws ' ')


parseReplCommand : String -> Result ReplCommand
parseReplCommand w_cmdStr = do
    let cmdStr = eatWhitespace (unpack w_cmdStr)
    case cmdStr of
        [] => Right Nop
        (':' :: xs) => do
            let xs' = eatWhitespace xs
            (cmd, rest) <- firstWordSplit xs'
            buildCommand cmd rest
        (x :: xs) => do
            term <- parseAndResolve_unpacked cmdStr
            success (MultiStep term)


execReplCommand : ReplState -> ReplCommand -> Result (Maybe (String, ReplState))
execReplCommand state (IsBNF term) = success $ Just (show $ decAsBool $ isInBNF term, state)
execReplCommand state (MultiStep term) =
    let (newTerm ** bnf) = betaMultiStep term in
    success $ Just (prettyPrint newTerm, state)
execReplCommand state (SingleStep term) = case betaSingleStep term of
    (Left newTerm) => success $ Just (prettyPrint newTerm, state)
    (Right bnf) => success $ Just ("Term already in BNF", state)
execReplCommand state Help = success $ Just (helpStr, state)
execReplCommand state Nop = success $ Just ("", state)
execReplCommand state Quit = success $ Nothing


-- execReplCommand (IsBNF term) = ?execReplCommand_rhs_1
-- execReplCommand (MultiStep term) = ?execReplCommand_rhs_2
-- execReplCommand (SingleStep term) = ?execReplCommand_rhs_3
-- execReplCommand Help = Just $ success helpStr
-- execReplCommand Nop = Just $ success ""
-- execReplCommand Quit = Nothing


replLoop : ReplState -> String -> Result (Maybe (String, ReplState))
replLoop state inputStr = do
    command <- parseReplCommand inputStr
    execReplCommand state command


replLoopWrapped : ReplState -> String -> Maybe (String, ReplState)
replLoopWrapped state x = case replLoop state x of
    (Left l) => Just ("Error: " ++ l ++ "\r\n", state)
    (Right Nothing) => Nothing
    (Right (Just (a, b))) => Just (a ++ "\r\n", b)

main : IO ()
main = replWith () "λ> " replLoopWrapped
