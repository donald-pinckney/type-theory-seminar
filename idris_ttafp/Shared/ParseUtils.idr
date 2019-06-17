module ParseUtils

export
isWhitespace : Char -> Bool
isWhitespace c = c == ' ' || c == '\n' || c == '\t' || c == '\r'

export
eatWhitespace : List Char -> List Char
eatWhitespace [] = []
eatWhitespace str@(x :: xs) =
    if isWhitespace x then
        eatWhitespace xs
    else
        str

export
eatOneChar : List Char -> Char -> List Char
eatOneChar [] c = []
eatOneChar (x :: xs) c = if x == c then xs else (x :: xs)


eatAndMatch_impl : List Char -> List Char -> (List Char, Bool)
eatAndMatch_impl [] [] = ([], True)
eatAndMatch_impl (x :: xs) [] = (x :: xs, True)
eatAndMatch_impl [] (y :: ys) = ([], False)
eatAndMatch_impl (x :: xs) (y :: ys) =
    if x == y then
        let (rest, didMatch) = eatAndMatch_impl xs ys in
        if didMatch then
            (rest, True)
        else
            ((x :: xs), False)
    else
        (x :: xs, False)

export
eatAndMatch : List Char -> String -> (List Char, Bool)
eatAndMatch xs x = eatAndMatch_impl xs (unpack x)
