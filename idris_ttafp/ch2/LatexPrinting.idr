module ch2.LatexPrinting

import ch2.Context
import ch2.Judgments
import ch2.AST
import Shared.Latex
import Shared.ElemAtIdx
import ch2.DerivationRules
import System

Latexify Type' True envs where
    latexify (VarType (FreeType x)) = math x
    latexify (Arrow x y) = math "(" ++ latexify x ++ math ") \\to " ++ latexify y

Latexify (String, Type') True envs where
    latexify (a, b) = math a ++ math " : " ++ latexify b

Latexify Term True envs where
    latexify (Var (Bound k)) = math "\\uparrow_{" ++ math (show k) ++ math "}"
    latexify (Var (Free x)) = math x
    latexify (App x y) = latexify x ++ math "(" ++ latexify y ++ math ")"
    latexify (Lambda x y) = math "\\lambda " ++ latexify x ++ math " . " ++ latexify y

Latexify a True envs => Latexify (List a) True envs where
    latexify [] = math "\\emptyset"
    latexify xs = concat (intersperse (math ", ") $ map latexify xs)

Latexify Context True envs where
    latexify (MkContext (x ** pf) boundDecls) = (latexify x) ++ math " ; " ++ (latexify boundDecls)

Latexify TypeJudgment True envs where
    latexify (MkTypeJudgment context term type) =
        latexify context ++ math " \\vdash " ++ latexify term ++ math " : " ++ latexify type

latexifyRule : List (LatexSource False envs) -> LatexSource True envs -> LatexSource False envs
latexifyRule hyps con =
    let hyps_cat = concat (intersperse (str "\\n") hyps) in
    addHeader "\\usepackage{bussproofs}" $ hyps_cat ++ case toIntegerNat (length hyps) of
        0 => str "\\AxiomC{" ++ inline con ++ str "}\n"
        1 => str "\\UnaryInfC{" ++ inline con ++ str "}\n"
        2 => str "\\BinaryInfC{" ++ inline con ++ str "}\n"
        3 => str "\\TrinaryInfC{" ++ inline con ++ str "}\n"
        4 => str "\\QuaternaryInfC{" ++ inline con ++ str "}\n"
        5 => str "\\QuinaryInfC{" ++ inline con ++ str "}\n"
        _ => str "\\GenericError{}{More than 5 hypotheses in derivation rule}{}{}%"


Latexify a True envs => Latexify (ElemAtIdx {a} v xs n) False envs where
    latexify {v} {xs} {n} _ = latexifyRule [] $ math "[" ++ latexify xs ++ math "][" ++ math (show n) ++ math "] = " ++ latexify v

Latexify (ValueAtKey v xs k) False envs where
    latexify {v} {xs} {k} _ = latexifyRule [] $ math "\\{" ++ latexify xs ++ math "\\}[``" ++ math k ++ math "''] = " ++ latexify v

Latexify (Holds j) False envs where
    latexify {j} {envs = []} h = beginEnd "prooftree" (latexify h)

    latexify {j = jd@(MkTypeJudgment gamma (Var (Bound n)) sigma)} (VarBound h1) =
        let tex1 = latexify h1 in
        let texJ = latexify jd in
        latexifyRule [tex1] texJ
    latexify {j = jd@(MkTypeJudgment gamma (Var (Free v)) sigma)} (VarFree h1) =
        let tex1 = latexify h1 in
        let texJ = latexify jd in
        latexifyRule [tex1] texJ
    latexify {j = jd@(MkTypeJudgment gamma (App m n) tau)} (ApplRule h1 h2) =
        let tex1 = latexify h1 in
        let tex2 = latexify h2 in
        let texJ = latexify jd in
        latexifyRule [tex1, tex2] texJ
    latexify {j = jd@(MkTypeJudgment gamma (Lambda sigma m) (Arrow sigma tau))} (AbstRule h1) =
        let tex1 = latexify h1 in
        let texJ = latexify jd in
        latexifyRule [tex1] texJ

export
writeLatexFile : String -> Holds j -> IO ()
writeLatexFile pathBase h = do
    let doc = latexDocument h
    Right () <- writeFile (pathBase ++ ".tex") doc
        | Left err => putStrLn ("Error: " ++ show err)

    system ("pdflatex " ++ pathBase ++ ".tex")
    system ("open " ++ pathBase ++ ".pdf")

    pure ()
