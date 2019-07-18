module Main

import ch1.Repl
import ch2.Repl
import defs.DefsMain


main : IO ()
main = defs_main


export
mainTests : IO ()
mainTests = pure ()
