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
