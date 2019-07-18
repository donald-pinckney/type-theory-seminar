module defs.Main

import defs.Parse
import Result
import defs.CST
import defs.Resolve
import defs.AST

export
defs_main : String -> IO ()
defs_main path = do
    Right str <- readFile path
        | Left err => putStrLn (path ++ ": " ++ show err)

    let Right cst = parse str
        | Left err => putStrLn ("Parse error: " ++ err)

    let Right ast = resolve cst
        | Left err => putStrLn ("Resolve error: " ++ err)

    putStrLn (show ast)

    -- pure ()
export
main : IO ()
main = do
    args <- getArgs
    case inBounds 1 args of
        (Yes prf) =>
            let path = index 1 args in
            defs_main path
        (No contra) => putStrLn "filename argument expected."
