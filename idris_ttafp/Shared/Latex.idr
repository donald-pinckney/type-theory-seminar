module Shared.Latex


export
record LatexSource (mathMode : Bool) (envs : List String) where
    constructor MkLatexSource
    text : String
    requiredHeaders : List String

export
str : String -> LatexSource False envs
str x = MkLatexSource x []

export
math : String -> LatexSource True envs
math x = MkLatexSource x []

export
inline : LatexSource True envs -> LatexSource False envs
inline (MkLatexSource text requiredHeaders) = MkLatexSource ("$" ++ text ++ "$") requiredHeaders

export
addHeader : String -> LatexSource m envs -> LatexSource m envs
addHeader h (MkLatexSource text requiredHeaders) = MkLatexSource text (union requiredHeaders [h])

export
beginEnd : (env : String) -> LatexSource m (env :: envs) -> LatexSource m envs
beginEnd env (MkLatexSource text requiredHeaders) = MkLatexSource ("\\begin{" ++ env ++ "}\n" ++ text ++ "\n\\end{" ++ env ++ "}\n") requiredHeaders

export
(++) : LatexSource m envs -> LatexSource m envs -> LatexSource m envs
(++) (MkLatexSource text requiredHeaders) (MkLatexSource x y) = MkLatexSource (text ++ x) (union requiredHeaders y)

public export
interface Latexify a (m : Bool) (envs : List String) where
    latexify : a -> LatexSource m envs

export
Semigroup (LatexSource m envs) where
    (<+>) = (++)

export
Monoid (LatexSource m envs) where
    neutral = MkLatexSource "" []

export
latexDocument : Latexify a False [] => a -> String
latexDocument x =
    let tex = latexify {m=False} {envs=[]} x in
    "\\documentclass[letterpaper]{article}\n" ++
        (unlines $ requiredHeaders tex) ++
        "\\begin{document}\n" ++
        text tex ++
        "\\end{document}\n"


-- export
