module defs.Parse

import ParseUtils
import Result
import TestingSupport
import defs.CST
import defs.Identifier


ParseResultInternal : Type -> Type
ParseResultInternal t = Result (t, SourceString)

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

parseIdentifier : SourceString -> SourceString -> ParseResultInternal Identifier
parseIdentifier acc [] = success (MkIdentifier acc, [])
parseIdentifier acc vStr@((nx, cx) :: xs) =
    if isVarChar cx then
        parseIdentifier (acc ++ [(nx, cx)]) xs
    else if isWhitespace cx then
        success (MkIdentifier acc, xs)
    else if length acc == 0 then
        error "Expected variable to parse"
    else
        success (MkIdentifier acc, vStr)




--
-- mutual
--     parseArrowFactor : SourceString -> ParseResultInternal (Either CType CDecl)
--     parseArrowFactor [] = error "Exepcted arrow type LHS to parse"
--     parseArrowFactor ((nx, '(') :: xs) = do
--         let xs = eatWhitespace xs
--         (t, xs) <- parseTypeOrDecl xs
--         let xs = eatWhitespace xs
--         xs <- expect xs ')'
--         pure (t, xs)
--     parseArrowFactor xs = do
--         let xs = eatWhitespace xs
--         (tv, xs) <- parseIdentifier [] xs
--         let xs = eatWhitespace xs
--         case eatAndMatch xs ":" of
--             (rest, False) => success (Left $ CTypeVariable tv, rest)
--             (rest, True) => do
--                 let xs = eatWhitespace rest
--                 (t, xs) <- parseType xs
--                 success (Right $ MkCDecl tv t, xs)
--
--     -- *a         ->    a*
--     -- *a -> b    ->    a -> b*
--     parseTypeOrDecl : SourceString -> ParseResultInternal (Either CType CDecl)
--     parseTypeOrDecl [] = error "Expected type to parse"
--     parseTypeOrDecl xs = do
--         let xs = eatWhitespace xs
--         (t, xs) <- parseArrowFactor xs
--         let xs = eatWhitespace xs
--         case eatAndMatch xs "->" of
--             (rest, True) => do
--                 (arrowRHS, rest) <- parseType (eatWhitespace rest)
--                 pure (Left $ CTypeArrow t arrowRHS, rest)
--             (rest, False) => pure (t, rest)
--
--     parseType : SourceString -> ParseResultInternal CType
--     parseType xs = do
--         (t, xs) <- parseTypeOrDecl xs
--         case t of
--             Left t' => success (t', xs)
--             Right d => error "Declaration not allowed here."
--
--
--

groupApps : CExpr -> List CExpr -> CExpr
groupApps acc [] = acc
groupApps acc (t :: ts) = groupApps (CExprApp acc t) ts


mutual

    -- *xe:a, y : b, zr:c.   ->   xe:a, *y : b, zr:c.
    -- xe:a, y : b, *zr:c.   ->   xe:a, y : b, zr:c*.
    parseVarAndType : SourceString -> ParseResultInternal CDecl
    parseVarAndType xs = do
        (v, xs) <- parseIdentifier [] xs
        let xs = eatWhitespace xs
        xs <- expect xs ':'
        let xs = eatWhitespace xs
        (t, xs) <- parseTerm xs
        let xs = eatWhitespace xs
        let xs = eatOneChar xs ','
        let xs = eatWhitespace xs
        pure (MkCDecl v t, xs)


    -- *x, y, z.   ->   x, y, z.*
    parseLambdaVars : SourceString -> ParseResultInternal (List CDecl)
    parseLambdaVars ((nx, '.') :: xs) = success ([], xs)
    parseLambdaVars varsStr = do
        (varAndType, rest) <- parseVarAndType (eatWhitespace varsStr)
        (moreVarsAndTypes, rest2) <- parseLambdaVars rest
        pure (varAndType :: moreVarsAndTypes, rest2)



    -- Something like \x y z.M
    -- But this starts with '\' already removed.
    parseLambda : SourceString -> ParseResultInternal CExpr
    parseLambda str = do
        (varsAndTypes, bodyStr) <- parseLambdaVars str
        (body, rest) <- parseTerm bodyStr
        pure (CExprLambda varsAndTypes body, rest)


    parseArrowFactor : SourceString -> ParseResultInternal (Either CExpr CDecl)
    parseArrowFactor [] = error "Expected input"
    parseArrowFactor str@((nx, '\\') :: xs) = case parseLambda xs of
        (Left l) => Left l
        (Right (e, r)) => Right (Left e, r)
    parseArrowFactor str@((nx, '(') :: xs) = do
        (t, r1) <- parseTerm xs
        let r1 = eatWhitespace r1
        case eatAndMatch r1 ":" of
            (r1, True) =>
                case t of
                    (CExprVariable x) => do
                        let r1 = eatWhitespace r1
                        (tt, r2) <- parseTerm r1
                        let r2 = eatWhitespace r2
                        r2 <- expect r2 ')'
                        success (Right $ MkCDecl x tt, r2)
                    _ => error "Variable name expected in declaration."
            (r1, False) => do
                r2 <- expect r1 ')'
                pure (Left t, r2)
    parseArrowFactor str = do
        (vStr, rest) <- parseIdentifier [] str
        pure (Left $ CExprVariable vStr, rest)


    parseExprOrDecl : SourceString -> ParseResultInternal (Either CExpr CDecl)
    parseExprOrDecl [] = error "Expected expr to parse"
    parseExprOrDecl xs = do
        let xs = eatWhitespace xs
        (t, xs) <- parseArrowFactor xs
        let xs = eatWhitespace xs
        case eatAndMatch xs "->" of
            (rest, True) => do
                (arrowRHS, rest) <- parseTerm (eatWhitespace rest)
                pure (Left $ CExprArrow t arrowRHS, rest)
            (rest, False) => pure (t, rest)


    parseAppFactor : SourceString -> ParseResultInternal CExpr
    parseAppFactor xs = do
        (t, xs) <- parseExprOrDecl xs
        case t of
            Left t' => success (t', xs)
            Right d => error "Declaration not allowed here."


    parseTermList : SourceString -> ParseResultInternal (List CExpr)
    parseTermList [] = success ([], [])
    parseTermList str@((nx, cx) :: xs) =
            if not (isStartOfTerm cx) then
                pure ([], str)
            else do
                (t, rest) <- parseAppFactor str
                let rest2 = eatWhitespace rest
                (ts, rest3) <- parseTermList rest2
                pure (t :: ts, rest3)

    parseTerm : SourceString -> ParseResultInternal CExpr
    parseTerm w_str = do
        let str = eatWhitespace w_str
        (tList, rest) <- parseTermList str
        case tList of
            t :: ts => success (groupApps t ts, rest)
            [] => error "Expected to parse term"



parseExpr_sexp : SourceString -> ParseResultInternal CExpr
parseExpr_sexp str = do
    str <- expect str '('
    (e, str) <- parseTerm str
    str <- expect str ')'
    success (e, str)


parseIdentifierList : SourceString -> ParseResultInternal (List Identifier)
parseIdentifierList str@((nx, cx) :: cs) =
    if isWhitespace cx then
        parseIdentifierList (eatWhitespace str)
    else if isVarChar cx then
        do
            (x, str) <- parseIdentifier [] str
            let str = eatWhitespace str
            (xs, str) <- parseIdentifierList str
            let str = eatWhitespace str
            success (x :: xs, str)
    else
        success ([], str)



mutual
    parseLine : SourceString -> ParseResultInternal CLine
    parseLine str = do
        str <- expect str '('
        let str = eatWhitespace str
        case eatAndMatch str "Suppose " of
            (str, True) => do
                let str = eatWhitespace str
                (x, str) <- parseIdentifier [] str
                let str = eatWhitespace str
                (t, str) <- parseExpr_sexp str
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
                        (x, str) <- parseIdentifier [] str
                        let str = eatWhitespace str
                        str <- expect str '('
                        (params, str) <- parseIdentifierList str
                        let str = eatWhitespace str
                        str <- expect str ')'
                        let str = eatWhitespace str
                        (e, str) <- parseExpr_sexp str
                        let str = eatWhitespace str
                        (t, str) <- parseExpr_sexp str
                        let str = eatWhitespace str
                        str <- expect str ')'
                        success (CLineDef (MkCDef x params e t), str)

    parseBook : SourceString -> ParseResultInternal CBook
    parseBook [] = success $ ([], [])
    parseBook str@((nx, ')') :: rest) = success $ ([], str)
    parseBook str = do
        let str2 = eatWhitespace str
        (line, str3) <- parseLine str2
        let str4 = eatWhitespace str3
        (rest, str5) <- parseBook str4
        success $ (line :: rest, str5)

export
parse_unpacked : SourceString -> Result CBook
parse_unpacked str = do
    let Right (parsed, []) = parseBook $ str
        | Left err => Left err
        | Right (parsed, remainingStr) =>
            Left ("Remaining input not parsed: " ++ packSource remainingStr)
    success parsed

export
parse : String -> Result CBook
parse str = parse_unpacked (unpackSource str)


------------------ Tests -----------------

x : Identifier
x = MkIdentifier $ unpackSource "x"

a : Identifier
a = MkIdentifier $ unpackSource "a"

b : Identifier
b = MkIdentifier $ unpackSource "b"

c : Identifier
c = MkIdentifier $ unpackSource "c"

t : Identifier
t = MkIdentifier $ unpackSource "t"

T : Identifier
T = MkIdentifier $ unpackSource "T"

U : Identifier
U = MkIdentifier $ unpackSource "U"

x' : CExpr
x' = CExprVariable x

a' : CExpr
a' = CExprVariable a

b' : CExpr
b' = CExprVariable b

c' : CExpr
c' = CExprVariable c

T' : CExpr
T' = CExprVariable T

U' : CExpr
U' = CExprVariable U

export
parseTests : IO ()
parseTests = makeTest [
    parse "" ===? [],
    parse "(Def x (a b c) (a (b c)) (T)) (Def b (a b c) (a b c) (T -> U))"
        ===? [CLineDef $ MkCDef x [a, b, c] (CExprApp a' (CExprApp b' c')) T',
              CLineDef $ MkCDef b [a, b, c] (CExprApp (CExprApp a' b') c') (CExprArrow (Left T') U')],
    parse "(Def x (a b c) (a (b c)) (T)) (Def b (a b c) (a b c) ((t : T) -> U))"
        ===? [CLineDef $ MkCDef x [a, b, c] (CExprApp a' (CExprApp b' c')) T',
              CLineDef $ MkCDef b [a, b, c] (CExprApp (CExprApp a' b') c') (CExprArrow (Right (MkCDecl t T')) U')],
    parse "(Suppose x (T -> U) (Def x (a b c) (a (b c)) (T)))"
        ===? [CLineSuppose (MkCDecl x (CExprArrow (Left T') U')) [CLineDef $ MkCDef x [a, b, c] (CExprApp a' (CExprApp b' c')) T']]
]
