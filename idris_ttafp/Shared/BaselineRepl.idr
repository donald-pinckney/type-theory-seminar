module BaselineRepl

import Baseline

baselineReplWith_loop : a -> String -> (a -> String -> IO (Maybe (String, a))) -> IO ()
baselineReplWith_loop state prompt f = do
    Just line <- baseline prompt
        | Nothing => pure ()

    Just (out, state') <- f state line
        | Nothing => pure ()

    putStr out
    baselineReplWith_loop state' prompt f

export
baselineReplWith : {default [] completions : List String} -> a -> String -> (a -> String -> IO (Maybe (String, a))) -> IO ()
baselineReplWith {completions} state prompt f = do
    readHistory ".history"
    addDictEntries completions
    baselineReplWith_loop state prompt f
    writeHistory ".history"
