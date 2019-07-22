module Shared.AbstractRepl

import Shared.ParseUtils
import Shared.Result
import Shared.BaselineRepl

-- First, just some random util stuff

joinBy : List (List a) -> a -> List a
joinBy [] s = []
joinBy [xs] s = xs
joinBy (x :: xs) s = x ++ s :: (joinBy xs s)

firstWordSplit : SourceString -> Result (SourceString, SourceString)
firstWordSplit xs =
    let words = split (\p => snd p == ' ') xs in
    case words of
        [] => error "Expected word"
        (w :: ws) => success (w, joinBy ws (0, ' '))



public export
ReplCommand : Type -> Type
ReplCommand stateType = stateType -> IO (Result (Maybe (String, stateType)))

public export
record CommandBuilder stateType where
    constructor MkCommandBuilder
    commandStrs : List (List Char)
    buildFn : SourceString -> Result (ReplCommand stateType)
    argStrs : String
    docStrs : String

helpRow : CommandBuilder stateType -> String
helpRow (MkCommandBuilder commandStrs buildFn argStrs docStrs) =
    let commandsStr = unwords $ map (\cmdStr => ":" ++ pack cmdStr) commandStrs in
    commandsStr ++ " " ++ argStrs ++ "\r\n\t" ++ docStrs


execReplCommand : stateType -> ReplCommand stateType -> IO (Result (Maybe (String, stateType)))
execReplCommand state f = f state


Command_nop : ReplCommand stateType
Command_nop state = pure $ success $ Just ("", state)

Command_quit : ReplCommand stateType
Command_quit state = pure $ success $ Nothing



parameters (supportedCommands : List (CommandBuilder stateType), ok : NonEmpty supportedCommands)
    mutual
        helpStr : String
        helpStr = unlines $ map helpRow actualSupportedCommands

        Command_help : ReplCommand stateType
        Command_help state = pure $ success $ Just (helpStr, state)

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


    buildCommand : SourceString -> SourceString -> Result (ReplCommand stateType)
    buildCommand cmd rest =
        case find (\b => any (== toChars cmd) (commandStrs b)) actualSupportedCommands of
            Nothing => error $ "Unrecognized command: :" ++ (pack $ toChars cmd) ++ ". Type :help to see a list of supported commands."
            (Just b) => (buildFn b) rest

    buildDefaultCommand : SourceString -> Result (ReplCommand stateType)
    buildDefaultCommand rest = (buildFn (head supportedCommands)) rest


    parseReplCommand : String -> Result (ReplCommand stateType)
    parseReplCommand w_cmdStr = do
        let cmdStr = eatWhitespace (unpackSource w_cmdStr)
        case cmdStr of
            [] => Right Command_nop
            ((n, ':') :: xs) => do
                let xs' = eatWhitespace xs
                (cmd, rest) <- firstWordSplit xs'
                buildCommand cmd rest
            (x :: xs) => buildDefaultCommand cmdStr


    replLoop : stateType -> String -> IO (Result (Maybe (String, stateType)))
    replLoop state inputStr = case parseReplCommand inputStr of
        (Left err) => pure (Left err)
        (Right command) => execReplCommand state command

    replLoopWrapped : stateType -> String -> IO (Maybe (String, stateType))
    replLoopWrapped state x = do
        res <- replLoop state x
        case res of
            (Left l) => pure $ Just ("Error: " ++ l ++ "\r\n", state)
            (Right Nothing) => pure Nothing
            (Right (Just (a, b))) => pure $ Just (a ++ "\r\n", b)

    export
    replMain : stateType -> IO ()
    replMain initialState = baselineReplWith {completions=completions} initialState "λ> " replLoopWrapped
