module AbstractRepl

import AST
import Resolve
import BetaNormalForm
import BetaReduction
import ParseUtils
import Result
import PrettyPrint


ReplState : Type
ReplState = ()

ReplCommand : Type
ReplCommand = ReplState -> Result (Maybe (String, ReplState))


Command_isBNF : Term -> ReplCommand
Command_isBNF term state = success $ Just (show $ decAsBool $ isInBNF term, state)

Command_multiStep : Term -> ReplCommand
Command_multiStep term state =
    let (newTerm ** bnf) = betaMultiStep term in
    success $ Just (prettyPrint newTerm, state)

Command_singleStep : Term -> ReplCommand
Command_singleStep term state = case betaSingleStep term of
    (Left newTerm) => success $ Just (prettyPrint newTerm, state)
    (Right bnf) => success $ Just ("Term already in BNF", state)

Command_nop : ReplCommand
Command_nop state = success $ Just ("", state)

Command_quit : ReplCommand
Command_quit state = success $ Nothing


record CommandBuilder where
    constructor MkCommandBuilder
    commandStrs : List (List Char)
    buildFn : List Char -> Result ReplCommand
    argStrs : String
    docStrs : String


mutual
    Command_help : ReplCommand
    Command_help state = success $ Just (helpStr, state)

    supportedCommands : List CommandBuilder
    supportedCommands = [
        MkCommandBuilder [['i','s','B','N','F']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_isBNF)) "<term>" "Tests if <term> is in BNF, and gives a proof.",
        MkCommandBuilder [['s','t','e','p']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_singleStep)) "<term>" "Performs one step of beta reduction on <term>.",
        MkCommandBuilder [['e'],['e','v','a','l']] (\rest => (parseAndResolve_unpacked rest) >>= (pure . Command_multiStep)) "<term>" "Performs beta multistep on <term> until it is in BNF.",
        MkCommandBuilder [['?'],['h'],['h','e','l','p']] (\rest => pure Command_help) "" "Display this help text.",
        MkCommandBuilder [['q'],['q','u','i','t']] (\rest => pure Command_quit) "" "Quits."
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
        [] => Right Command_nop
        (':' :: xs) => do
            let xs' = eatWhitespace xs
            (cmd, rest) <- firstWordSplit xs'
            buildCommand cmd rest
        (x :: xs) => do
            term <- parseAndResolve_unpacked cmdStr
            success (Command_multiStep term)


execReplCommand : ReplState -> ReplCommand -> Result (Maybe (String, ReplState))
execReplCommand state f = f state

replLoop : ReplState -> String -> Result (Maybe (String, ReplState))
replLoop state inputStr = do
    command <- parseReplCommand inputStr
    execReplCommand state command


replLoopWrapped : ReplState -> String -> Maybe (String, ReplState)
replLoopWrapped state x = case replLoop state x of
    (Left l) => Just ("Error: " ++ l ++ "\r\n", state)
    (Right Nothing) => Nothing
    (Right (Just (a, b))) => Just (a ++ "\r\n", b)

export
replMain : IO ()
replMain = replWith () "λ> " replLoopWrapped
