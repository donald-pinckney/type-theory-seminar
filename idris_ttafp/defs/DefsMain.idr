module defs.DefsMain

import defs.Parse
import Shared.Result
import defs.CST
import defs.Resolve
import defs.AST
import defs.TypeCheck
import defs.BindingDepth
import System


failWithError : String -> IO ()
failWithError msg = do
    putStrLn msg
    exitFailure


export
defs_main_path : String -> IO ()
defs_main_path path = do
    Right str <- readFile path
        | Left err => failWithError (path ++ ": " ++ show err)

    let Right cst = parse str
        | Left err => failWithError ("Parse error: " ++ err)

    let Right ast = resolve cst
        | Left err => failWithError ("Resolve error: " ++ err)

    putStrLn (show ast)

    let Right () = type_check_main ast
        | Left err => failWithError ("Type checking error: " ++ err)

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
