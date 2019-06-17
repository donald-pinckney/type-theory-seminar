module BaselineRepl

import Baseline

baselineReplWith_loop : a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
baselineReplWith_loop state prompt f = do
    str <- baseline prompt
    case str of
        Nothing => pure ()
        Just line => case f state line of
            Nothing => pure ()
            Just (out, state') => do
                putStr out
                baselineReplWith_loop state' prompt f

export
baselineReplWith : {default [] completions : List String} -> a -> String -> (a -> String -> Maybe (String, a)) -> IO ()
baselineReplWith {completions} state prompt f = do
    readHistory ".history"
    addDictEntries completions
    baselineReplWith_loop state prompt f
    writeHistory ".history"
