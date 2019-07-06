module defs.Parse

import ParseUtils
import Result
import TestingSupport
import defs.CST


ParseResultInternal : Type -> Type
ParseResultInternal t = Result (t, List Char)

expect : List Char -> Char -> Result (List Char)
expect [] c = error $ "Expected '" ++ (singleton c) ++ "', but no input left."
expect (x :: xs) c =
    if x == c then
        success xs
    else
        error $ "Expected '" ++ (singleton c) ++ "', got '" ++ (singleton x) ++ "'"

isVarChar : Char -> Bool
isVarChar c = isAlpha c || isDigit c || (
    let n = ord c in
    (33 <= n && n <= 39)
        || (42 <= n && n <= 43)
        || (47 == n)
        || (59 <= n && n <= 61)
        || (63 <= n && n <= 64)
        || (91 == n)
        || (93 == n)
        || (94 <= n && n <= 96)
        || (123 <= n && n <= 126)
)

isStartOfTerm : Char -> Bool
isStartOfTerm c = isVarChar c || c == '(' || c == '\\'




parseIdentifier : String -> List Char -> ParseResultInternal Identifier
parseIdentifier acc [] = success (MkIdentifier acc, [])
parseIdentifier acc vStr@(x :: xs) =
    if isVarChar x then
        parseIdentifier (acc ++ (singleton x)) xs
    else if isWhitespace x then
        success (MkIdentifier acc, xs)
    else if length acc == 0 then
        error "Expected variable to parse"
    else
        success (MkIdentifier acc, vStr)





mutual
    parseArrowFactor : List Char -> ParseResultInternal CType
    parseArrowFactor [] = error "Exepcted arrow type LHS to parse"
    parseArrowFactor ('(' :: xs) = do
        let xs = eatWhitespace xs
        (t, xs) <- parseType xs
        let xs = eatWhitespace xs
        xs <- expect xs ')'
        pure (t, xs)
    parseArrowFactor xs = do
        let xs = eatWhitespace xs
        (tv, xs) <- parseIdentifier "" xs
        let xs = eatWhitespace xs
        success (CTypeVariable tv, xs)

    -- *a         ->    a*
    -- *a -> b    ->    a -> b*
    parseType : List Char -> ParseResultInternal CType
    parseType [] = error "Expected type to parse"
    parseType xs = do
        let xs = eatWhitespace xs
        (t, xs) <- parseArrowFactor xs
        let xs = eatWhitespace xs
        case eatAndMatch xs "->" of
            (rest, True) => do
                (arrowRHS, rest) <- parseType (eatWhitespace rest)
                pure (CTypeArrow t arrowRHS, rest)
            (rest, False) => pure (t, rest)




-- *xe:a, y : b, zr:c.   ->   xe:a, *y : b, zr:c.
-- xe:a, y : b, *zr:c.   ->   xe:a, y : b, zr:c*.
parseVarAndType : List Char -> ParseResultInternal CDecl
parseVarAndType xs = do
    (v, xs) <- parseIdentifier "" xs
    let xs = eatWhitespace xs
    xs <- expect xs ':'
    let xs = eatWhitespace xs
    (t, xs) <- parseType xs
    let xs = eatWhitespace xs
    let xs = eatOneChar xs ','
    let xs = eatWhitespace xs
    pure (MkCDecl v t, xs)

-- *x, y, z.   ->   x, y, z.*
parseLambdaVars : List Char -> ParseResultInternal (List CDecl)
parseLambdaVars ('.' :: xs) = success ([], xs)
parseLambdaVars varsStr = do
    -- ?pouwer
    (varAndType, rest) <- parseVarAndType $ unpack $ trim $ pack varsStr
    (moreVarsAndTypes, rest2) <- parseLambdaVars rest
    pure (varAndType :: moreVarsAndTypes, rest2)


groupApps : CExpr -> List CExpr -> CExpr
groupApps acc [] = acc
groupApps acc (t :: ts) = groupApps (CExprApp acc t) ts

mutual

    -- Something like \x y z.M
    -- But this starts with '\' already removed.
    parseLambda : List Char -> ParseResultInternal CExpr
    parseLambda str = do
        (varsAndTypes, bodyStr) <- parseLambdaVars str
        (body, rest) <- parseTerm bodyStr
        pure (CExprLambda varsAndTypes body, rest)


    parseTermSingle : List Char -> ParseResultInternal CExpr
    parseTermSingle [] = error "Expected input"
    parseTermSingle str@('\\' :: xs) = parseLambda xs
    parseTermSingle str@('(' :: xs) = do
        (t, r1) <- parseTerm xs
        r2 <- expect r1 ')'
        pure (t, r2)
    parseTermSingle str = do
        (vStr, rest) <- parseIdentifier "" str
        pure (CExprVariable vStr, rest)

    parseTermList : List Char -> ParseResultInternal (List CExpr)
    parseTermList [] = success ([], [])
    parseTermList str@(x :: xs) =
            if not (isStartOfTerm x) then
                pure ([], str)
            else do
                (t, rest) <- parseTermSingle str
                let rest2 = eatWhitespace rest
                (ts, rest3) <- parseTermList rest2
                pure (t :: ts, rest3)

    parseTerm : List Char -> ParseResultInternal CExpr
    parseTerm w_str = do
        let str = eatWhitespace w_str
        (tList, rest) <- parseTermList str
        case tList of
            t :: ts => success (groupApps t ts, rest)
            [] => error "Expected to parse term"




parseExpr_sexp : List Char -> ParseResultInternal CExpr
parseExpr_sexp str = do
    str <- expect str '('
    (e, str) <- parseTerm str
    str <- expect str ')'
    success (e, str)

parseType_sexp : List Char -> ParseResultInternal CType
parseType_sexp str = do
    str <- expect str '('
    (t, str) <- parseType str
    str <- expect str ')'
    success (t, str)

parseIdentifierList : List Char -> ParseResultInternal (List Identifier)
parseIdentifierList str@(c :: cs) =
    if isWhitespace c then
        parseIdentifierList (eatWhitespace str)
    else if isVarChar c then
        do
            (x, str) <- parseIdentifier "" str
            let str = eatWhitespace str
            (xs, str) <- parseIdentifierList str
            let str = eatWhitespace str
            success (x :: xs, str)
    else
        success ([], str)


mutual
    parseLine : List Char -> ParseResultInternal CLine
    parseLine str = do
        str <- expect str '('
        case eatAndMatch str "Suppose " of
            (str, True) => do
                let str = eatWhitespace str
                (x, str) <- parseIdentifier "" str
                let str = eatWhitespace str
                (t, str) <- parseType_sexp str
                let str = eatWhitespace str
                (b, str) <- parseBook str
                let str = eatWhitespace str
                str <- expect str ')'
                success $ (CLineSuppose (MkCDecl x t) b, str)
            (str, False) =>
                case eatAndMatch str "Def " of
                    (str, False) => error "Expected either 'Suppose' or 'Def'"
                    (str, True) => do
                        let str = eatWhitespace str
                        (x, str) <- parseIdentifier "" str
                        let str = eatWhitespace str
                        str <- expect str '('
                        (params, str) <- parseIdentifierList str
                        let str = eatWhitespace str
                        str <- expect str ')'
                        let str = eatWhitespace str
                        (e, str) <- parseExpr_sexp str
                        let str = eatWhitespace str
                        (t, str) <- parseType_sexp str
                        let str = eatWhitespace str
                        str <- expect str ')'
                        success (CLineDef (MkCDef x params e t), str)

    parseBook : List Char -> ParseResultInternal CBook
    parseBook [] = success $ ([], [])
    parseBook (')'::rest) = success $ ([], ')'::rest)
    parseBook str = do
        let str2 = eatWhitespace str
        (line, str3) <- parseLine str2
        let str4 = eatWhitespace str3
        (rest, str5) <- parseBook str4
        success $ (line :: rest, str5)

export
parse_unpacked : List Char -> Result CBook
parse_unpacked str = do
    let Right (parsed, []) = parseBook $ str
        | Left err => Left err
        | Right (parsed, remainingStr) =>
            Left ("Remaining input not parsed: " ++ pack remainingStr)
    success parsed

export
parse : String -> Result CBook
parse str = parse_unpacked (unpack str)


------------------ Tests -----------------

x : Identifier
x = MkIdentifier "x"

a : Identifier
a = MkIdentifier "a"

b : Identifier
b = MkIdentifier "b"

c : Identifier
c = MkIdentifier "c"

T : Identifier
T = MkIdentifier "T"

U : Identifier
U = MkIdentifier "U"

x' : CExpr
x' = CExprVariable x

a' : CExpr
a' = CExprVariable a

b' : CExpr
b' = CExprVariable b

c' : CExpr
c' = CExprVariable c

T' : CType
T' = CTypeVariable T

U' : CType
U' = CTypeVariable U

export
parseTests : IO ()
parseTests = makeTest [
    parse "" ===? [],
    parse "(Def x (a b c) (a (b c)) (T)) (Def b (a b c) (a b c) (T -> U))"
        ===? [CLineDef $ MkCDef x [a, b, c] (CExprApp a' (CExprApp b' c')) T',
              CLineDef $ MkCDef b [a, b, c] (CExprApp (CExprApp a' b') c') (CTypeArrow T' U')],
    parse "(Suppose x (T -> U) (Def x (a b c) (a (b c)) (T)))"
        ===? [CLineSuppose (MkCDecl x (CTypeArrow T' U')) [CLineDef $ MkCDef x [a, b, c] (CExprApp a' (CExprApp b' c')) T']]
    -- parseExpr_sexp (unpack "(xy)") ===? CExprVariable "xy",
    -- parseExpr_sexp (unpack "(x y)") ===? App (Variable "x") (Variable "y"),
    -- parseExpr_sexp (unpack "(x y z)") ===? App (App (Variable "x") (Variable "y")) (Variable "z"),
    -- parseExpr_sexp (unpack "(esdx zy zz)") ===? App (App (Variable "esdx") (Variable "zy")) (Variable "zz"),
    -- parseExpr_sexp (unpack "(x (y z))") ===? App (Variable "x") (App (Variable "y") (Variable "z")),
    -- parseExpr_sexp (unpack "(x(y z))") ===? App (Variable "x") (App (Variable "y") (Variable "z")),
    -- parseExpr_sexp (unpack "((x y) z)") ===? App (App (Variable "x") (Variable "y")) (Variable "z"),
    -- parseExpr_sexp (unpack "((x y)z)") ===? App (App (Variable "x") (Variable "y")) (Variable "z"),
    -- parseExpr_sexp (unpack "(\\x:a.x y)") ===? Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y")),
    -- parseExpr_sexp (unpack "(\\x : a. x y)") ===? Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y")),
    -- parseExpr_sexp (unpack "(\\xy:ab.x y)") ===? Lambda [("xy", TypeVariable "ab")] (App (Variable "x") (Variable "y")),
    -- parseExpr_sexp (unpack "(\\x:a,y:b .x y)") ===? Lambda [("x", TypeVariable "a"), ("y", TypeVariable "b")] (App (Variable "x") (Variable "y")),
    -- parseExpr_sexp (unpack "(\\x:a , y:b. x (y z))") ===? Lambda [("x", TypeVariable "a"), ("y", TypeVariable "b")] (App (Variable "x") (App (Variable "y") (Variable "z"))),
    -- parseExpr_sexp (unpack "((\\x:a.x y))") ===? Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y")),
    -- parseExpr_sexp (unpack "((\\x:a.x y)(\\y:b.x y))") ===? App (Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y"))) (Lambda [("y", TypeVariable "b")] (App (Variable "x") (Variable "y"))),
    -- parseExpr_sexp (unpack "(\\x:a.\\y:b.x(\\z:c.x z) w)") ===? Lambda [("x", TypeVariable "a")] (Lambda [("y", TypeVariable "b")] (App (App (Variable "x") (Lambda [("z", TypeVariable "c")] (App (Variable "x") (Variable "z")))) (Variable "w")))
]
