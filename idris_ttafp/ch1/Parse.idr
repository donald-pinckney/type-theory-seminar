module ch1.Parse

import Shared.ParseUtils
import Shared.Result
import Shared.TestingSupport

public export
data ParsedTerm =
    Variable String
    | App ParsedTerm ParsedTerm
    | Lambda (List String) ParsedTerm

Eq ParsedTerm where
    (Variable x) == (Variable y) = (x == y)
    (App a b) == (App c d) = (a == c) && (b == d)
    (Lambda xs a) == (Lambda ys b) = (xs == ys) && (a == b)
    _ == _ = False

Show ParsedTerm where
    show (Variable x) = x
    show (App x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"
    show (Lambda xs x) = "\\" ++ (unwords xs) ++ " . " ++ (show x)


ParseResultInternal : Type -> Type
ParseResultInternal t = Result (t, SourceString)


isVarChar : Char -> Bool
isVarChar c = isAlpha c || isDigit c || (
    let n = ord c in
    (33 <= n && n <= 39)
        || (42 <= n && n <= 43)
        || (45 == n)
        || (47 == n)
        || (58 <= n && n <= 64)
        || (91 == n)
        || (93 == n)
        || (94 <= n && n <= 96)
        || (123 <= n && n <= 126)
)

isStartOfTerm : Char -> Bool
isStartOfTerm c = isVarChar c || c == '(' || c == '\\'


-- *xe y zr.   ->   xe *y zr.
-- xe y *zr.   ->   xe y zr*.
parseVar : String -> SourceString -> ParseResultInternal String
parseVar acc [] = Right (acc, [])
parseVar acc vStr@((nx, cx) :: xs) =
    if isVarChar cx then
        parseVar (acc ++ (pack [cx])) xs
    else if isWhitespace cx then
        Right (acc, xs)
    else if length acc == 0 then
        Left "Expected variable to parse"
    else
        Right (acc, vStr)

-- *x y z.   ->   x y z.*
parseLambdaVars : SourceString -> ParseResultInternal (List String)
parseLambdaVars ((nx, '.') :: xs) = Right ([], xs)
parseLambdaVars varsStr = do
    (v, rest) <- parseVar "" $ unpackSource $ trim $ packSource varsStr
    (moreV, rest2) <- parseLambdaVars rest
    pure (v :: moreV, rest2)


groupApps : ParsedTerm -> List ParsedTerm -> ParsedTerm
groupApps acc [] = acc
groupApps acc (t :: ts) = groupApps (App acc t) ts

mutual

    -- Something like \x y z.M
    -- But this starts with '\' already removed.
    parseLambda : SourceString -> ParseResultInternal ParsedTerm
    parseLambda str = do
        (vars, bodyStr) <- parseLambdaVars str
        (body, rest) <- parseTerm bodyStr
        pure (Lambda vars body, rest)


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
parse_unpacked str = case parseTerm str of
    (Left err) => Left err
    (Right (parsed, [])) => Right parsed
    (Right (parsed, x :: xs)) => Left ("Remaining input not parsed: " ++ packSource (x :: xs))


-- parse_unpacked str = do
--     let Right (parsed, []) = parseTerm $ str
--         | Left err => Left err
--         | Right (parsed, remainingStr) =>
--             Left ("Remaining input not parsed: " ++ pack remainingStr)
--     pure parsed

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
    parse "\\x.x y" ===? Lambda ["x"] (App (Variable "x") (Variable "y")),
    parse "\\x. x y" ===? Lambda ["x"] (App (Variable "x") (Variable "y")),
    parse "\\xy.x y" ===? Lambda ["xy"] (App (Variable "x") (Variable "y")),
    parse "\\x y.x y" ===? Lambda ["x", "y"] (App (Variable "x") (Variable "y")),
    parse "\\x y.x (y z)" ===? Lambda ["x", "y"] (App (Variable "x") (App (Variable "y") (Variable "z"))),
    parse "(\\x.x y)" ===? Lambda ["x"] (App (Variable "x") (Variable "y")),
    parse "(\\x.x y)(\\y.x y)" ===? App (Lambda ["x"] (App (Variable "x") (Variable "y"))) (Lambda ["y"] (App (Variable "x") (Variable "y"))),
    parse "\\x.\\y.x(\\z.x z) w" ===? Lambda ["x"] (Lambda ["y"] (App (App (Variable "x") (Lambda ["z"] (App (Variable "x") (Variable "z")))) (Variable "w")))
]
