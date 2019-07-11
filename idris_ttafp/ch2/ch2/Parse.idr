module ch2.Parse

import ParseUtils
import Result
import TestingSupport

public export
data ParsedType =
      TypeVariable String
    | TypeArrow ParsedType ParsedType

Eq ParsedType where
    (TypeVariable a) == (TypeVariable b) = (a == b)
    (TypeArrow a b) == (TypeArrow c d) = (a == c) && (b == d)
    _ == _ = False

Show ParsedType where
    show (TypeVariable a) = a
    show (TypeArrow a b) = "(" ++ show a ++ ") -> (" ++ show b ++ ")"

public export
data ParsedTerm =
    Variable String
    | App ParsedTerm ParsedTerm
    | Lambda (List (String, ParsedType)) ParsedTerm

Eq ParsedTerm where
    (Variable x) == (Variable y) = (x == y)
    (App a b) == (App c d) = (a == c) && (b == d)
    (Lambda xs a) == (Lambda ys b) = (xs == ys) && (a == b)
    _ == _ = False

Show ParsedTerm where
    show (Variable x) = x
    show (App x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"
    show (Lambda xs x) = "\\" ++ (unwords $ map (\p => (fst p) ++ " : " ++ (show $ snd p)) xs) ++ " . " ++ (show x)


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




parseVar : String -> SourceString -> ParseResultInternal String
parseVar acc [] = Right (acc, [])
parseVar acc vStr@((nx, cx) :: xs) =
    if isVarChar cx then
        parseVar (acc ++ (singleton cx)) xs
    else if isWhitespace cx then
        Right (acc, xs)
    else if length acc == 0 then
        Left "Expected variable to parse"
    else
        Right (acc, vStr)

mutual
    parseArrowFactor : SourceString -> ParseResultInternal ParsedType
    parseArrowFactor [] = Left "Exepcted arrow type LHS to parse"
    parseArrowFactor ((nx, '(') :: xs) = do
        let xs = eatWhitespace xs
        (t, xs) <- parseType xs
        let xs = eatWhitespace xs
        xs <- expect xs ')'
        pure (t, xs)
    parseArrowFactor xs = do
        let xs = eatWhitespace xs
        (tv, xs) <- parseVar "" xs
        let xs = eatWhitespace xs
        pure (TypeVariable tv, xs)

    -- *a         ->    a*
    -- *a -> b    ->    a -> b*
    parseType : SourceString -> ParseResultInternal ParsedType
    parseType [] = Left "Expected type to parse"
    parseType xs = do
        let xs = eatWhitespace xs
        (t, xs) <- parseArrowFactor xs
        let xs = eatWhitespace xs
        case eatAndMatch xs "->" of
            (rest, True) => do
                (arrowRHS, rest) <- parseType (eatWhitespace rest)
                pure (TypeArrow t arrowRHS, rest)
            (rest, False) => pure (t, rest)




-- *xe:a, y : b, zr:c.   ->   xe:a, *y : b, zr:c.
-- xe:a, y : b, *zr:c.   ->   xe:a, y : b, zr:c*.
parseVarAndType : SourceString -> ParseResultInternal (String, ParsedType)
parseVarAndType xs = do
    (v, xs) <- parseVar "" xs
    let xs = eatWhitespace xs
    xs <- expect xs ':'
    let xs = eatWhitespace xs
    (t, xs) <- parseType xs
    let xs = eatWhitespace xs
    let xs = eatOneChar xs ','
    let xs = eatWhitespace xs
    pure ((v, t), xs)

-- *x, y, z.   ->   x, y, z.*
parseLambdaVars : SourceString -> ParseResultInternal (List (String, ParsedType))
parseLambdaVars ((nx, '.') :: xs) = Right ([], xs)
parseLambdaVars varsStr = do
    -- ?pouwer
    (varAndType, rest) <- parseVarAndType $ unpackSource $ trim $ packSource varsStr
    (moreVarsAndTypes, rest2) <- parseLambdaVars rest
    pure (varAndType :: moreVarsAndTypes, rest2)


groupApps : ParsedTerm -> List ParsedTerm -> ParsedTerm
groupApps acc [] = acc
groupApps acc (t :: ts) = groupApps (App acc t) ts

mutual

    -- Something like \x y z.M
    -- But this starts with '\' already removed.
    parseLambda : SourceString -> ParseResultInternal ParsedTerm
    parseLambda str = do
        (varsAndTypes, bodyStr) <- parseLambdaVars str
        (body, rest) <- parseTerm bodyStr
        pure (Lambda varsAndTypes body, rest)


    parseTermSingle : SourceString -> ParseResultInternal ParsedTerm
    parseTermSingle [] = Left "Expected input"
    parseTermSingle str@((nx, '\\') :: xs) = parseLambda xs
    parseTermSingle str@((nx, '(') :: xs) = do
        -- let a = unsafePerformIO {ffi=FFI_C} (do putStrLn "asdfasdf"; pure ())
        (t, r1) <- parseTerm xs
        r2 <- expect r1 ')'
        pure (t, r2)
    parseTermSingle str = do
        (vStr, rest) <- parseVar "" str
        pure (Variable vStr, rest)

    parseTermList : SourceString -> ParseResultInternal (List ParsedTerm)
    parseTermList [] = Right ([], [])
    parseTermList str@((nx, cx) :: xs) =
            if not (isStartOfTerm cx) then
                -- Left $ "expected start of term, instead got: " ++ (singleton x)
                pure ([], str)
            else do
                (t, rest) <- parseTermSingle str
                let rest2 = eatWhitespace rest
                (ts, rest3) <- parseTermList rest2
                pure (t :: ts, rest3)

    parseTerm : SourceString -> ParseResultInternal ParsedTerm
    parseTerm w_str = do
        let str = eatWhitespace w_str
        (tList, rest) <- parseTermList str
        case tList of
            t :: ts => Right (groupApps t ts, rest)
            [] => Left "Expected to parse term"


export
parse_unpacked : SourceString -> Result ParsedTerm
parse_unpacked str = do
    let Right (parsed, []) = parseTerm $ str
        | Left err => Left err
        | Right (parsed, remainingStr) =>
            Left ("Remaining input not parsed: " ++ packSource remainingStr)
    pure parsed

export
parse : String -> Result ParsedTerm
parse str = parse_unpacked (unpackSource str)


------------------ Tests -----------------



export
parseTests : IO ()
parseTests = makeTest [
    parse "xy" ===? Variable "xy",
    parse "x y" ===? App (Variable "x") (Variable "y"),
    parse "x y z" ===? App (App (Variable "x") (Variable "y")) (Variable "z"),
    parse "esdx zy zz" ===? App (App (Variable "esdx") (Variable "zy")) (Variable "zz"),
    parse "x (y z)" ===? App (Variable "x") (App (Variable "y") (Variable "z")),
    parse "x(y z)" ===? App (Variable "x") (App (Variable "y") (Variable "z")),
    parse "(x y) z" ===? App (App (Variable "x") (Variable "y")) (Variable "z"),
    parse "(x y)z" ===? App (App (Variable "x") (Variable "y")) (Variable "z"),
    parse "\\x:a.x y" ===? Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y")),
    parse "\\x : a. x y" ===? Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y")),
    parse "\\xy:ab.x y" ===? Lambda [("xy", TypeVariable "ab")] (App (Variable "x") (Variable "y")),
    parse "\\x:a,y:b .x y" ===? Lambda [("x", TypeVariable "a"), ("y", TypeVariable "b")] (App (Variable "x") (Variable "y")),
    parse "\\x:a , y:b. x (y z)" ===? Lambda [("x", TypeVariable "a"), ("y", TypeVariable "b")] (App (Variable "x") (App (Variable "y") (Variable "z"))),
    parse "(\\x:a.x y)" ===? Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y")),
    parse "(\\x:a.x y)(\\y:b.x y)" ===? App (Lambda [("x", TypeVariable "a")] (App (Variable "x") (Variable "y"))) (Lambda [("y", TypeVariable "b")] (App (Variable "x") (Variable "y"))),
    parse "\\x:a.\\y:b.x(\\z:c.x z) w" ===? Lambda [("x", TypeVariable "a")] (Lambda [("y", TypeVariable "b")] (App (App (Variable "x") (Lambda [("z", TypeVariable "c")] (App (Variable "x") (Variable "z")))) (Variable "w")))
]
