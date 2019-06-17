module AbstractRepl

import ParseUtils
import Result
import BaselineRepl

-- First, just some random util stuff

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



public export
ReplCommand : Type -> Type
ReplCommand stateType = stateType -> Result (Maybe (String, stateType))

public export
record CommandBuilder stateType where
    constructor MkCommandBuilder
    commandStrs : List (List Char)
    buildFn : List Char -> Result (ReplCommand stateType)
    argStrs : String
    docStrs : String

helpRow : CommandBuilder stateType -> String
helpRow (MkCommandBuilder commandStrs buildFn argStrs docStrs) =
    let commandsStr = unwords $ map (\cmdStr => ":" ++ pack cmdStr) commandStrs in
    commandsStr ++ " " ++ argStrs ++ "\r\n\t" ++ docStrs


execReplCommand : stateType -> ReplCommand stateType -> Result (Maybe (String, stateType))
execReplCommand state f = f state


Command_nop : ReplCommand stateType
Command_nop state = success $ Just ("", state)

Command_quit : ReplCommand stateType
Command_quit state = success $ Nothing



parameters (supportedCommands : List (CommandBuilder stateType), ok : NonEmpty supportedCommands)
    mutual
        helpStr : String
        helpStr = unlines $ map helpRow actualSupportedCommands

        Command_help : ReplCommand stateType
        Command_help state = success $ Just (helpStr, state)

        actualSupportedCommands : List (CommandBuilder stateType)
        actualSupportedCommands = supportedCommands ++ [
            MkCommandBuilder [['?'],['h'],['h','e','l','p']] (\rest => pure Command_help) "" "Display this help text.",
            MkCommandBuilder [['q'],['q','u','i','t']] (\rest => pure Command_quit) "" "Quits."
        ]

    completions : List String
    completions =
        let commands' = map commandStrs actualSupportedCommands in
        let commands = join commands' in
        map (strCons ':' . pack) commands


    buildCommand : List Char -> List Char -> Result (ReplCommand stateType)
    buildCommand cmd rest =
        case find (\b => any (==cmd) (commandStrs b)) actualSupportedCommands of
            Nothing => error $ "Unrecognized command: :" ++ (pack cmd) ++ ". Type :help to see a list of supported commands."
            (Just b) => (buildFn b) rest

    buildDefaultCommand : List Char -> Result (ReplCommand stateType)
    buildDefaultCommand rest = (buildFn (head supportedCommands)) rest


    parseReplCommand : String -> Result (ReplCommand stateType)
    parseReplCommand w_cmdStr = do
        let cmdStr = eatWhitespace (unpack w_cmdStr)
        case cmdStr of
            [] => Right Command_nop
            (':' :: xs) => do
                let xs' = eatWhitespace xs
                (cmd, rest) <- firstWordSplit xs'
                buildCommand cmd rest
            (x :: xs) => buildDefaultCommand cmdStr


    replLoop : stateType -> String -> Result (Maybe (String, stateType))
    replLoop state inputStr = do
        command <- parseReplCommand inputStr
        execReplCommand state command

    replLoopWrapped : stateType -> String -> Maybe (String, stateType)
    replLoopWrapped state x = case replLoop state x of
        (Left l) => Just ("Error: " ++ l ++ "\r\n", state)
        (Right Nothing) => Nothing
        (Right (Just (a, b))) => Just (a ++ "\r\n", b)

    export
    replMain : stateType -> IO ()
    replMain initialState = baselineReplWith {completions=completions} initialState "λ> " replLoopWrapped
