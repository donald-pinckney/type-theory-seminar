module defs.DefsMain

import defs.Parse
import Shared.Result
import defs.CST
import defs.Resolve
import defs.AST
import defs.TypeCheck

export
defs_main_path : String -> IO ()
defs_main_path path = do
    Right str <- readFile path
        | Left err => putStrLn (path ++ ": " ++ show err)

    let Right cst = parse str
        | Left err => putStrLn ("Parse error: " ++ err)

    let Right ast = resolve cst
        | Left err => putStrLn ("Resolve error: " ++ err)

    putStrLn (show ast)

    let Right () = type_check_main ast
        | Left err => putStrLn ("Type checking error: " ++ err)

    putStrLn "Type checking ok."

export
defs_main : IO ()
defs_main = do
    args <- getArgs
    case inBounds 1 args of
        (Yes prf) =>
            let path = index 1 args in
            defs_main_path path
        (No contra) => putStrLn "filename argument expected."
