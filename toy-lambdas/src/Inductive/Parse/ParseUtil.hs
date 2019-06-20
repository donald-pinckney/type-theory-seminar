module Inductive.Parse.ParseUtil
  ( makeParser
  -- | * Char parsers
  , parens
  , braces   
  , padded   
  , vbar     
  , uppercase
  , lowercase
  , alpha    
  , digit    
  , identchar
  -- | * String Parsers
  , alphanum
  , varNameStr
  , typeParamStr
  , typeNameStr
  -- | * List Parsers
  , commaSepList
  , commaSepList1
  , spaceSepList
  , spaceSepList1
  ) where

import GHC.Unicode ( isSpace )
import Text.ParserCombinators.ReadP
import Control.Applicative

-- | 'makeParser' takes a 'ReadP a' and returns a 'String' parser that returns a
-- 'Maybe a'. This function applies the provided 'ReadP a' to the input and
-- checks all the resulting parses. If any are complete (that is, all characters
-- are parsed) then it returns 'Just x', where 'x' is the result of a successful
-- complete parse. Otherwise, the function returns 'Nothing'.

makeParser :: ReadP a -> String -> Maybe a
makeParser p s = let parses = (readP_to_S p) s in
                     case (filter (null . snd) parses) of
                       (p : _) -> Just $ fst p
                       _ -> Nothing

-- -----------------------------------------------------------------------------
-- The following are all 'ReadP Char's

parens    = between (char '(') (char ')')
braces    = between (char '{') (char '}')
padded    = between skipSpaces skipSpaces
vbar      = (char '|')
uppercase = choice (map char ['A'..'Z'])
lowercase = choice (map char ['a'..'z'])
alpha     = uppercase <|> lowercase
digit     = choice (map char ['0'..'9'])
identchar = (char '_') <|> alpha <|> digit

-- -----------------------------------------------------------------------------
-- Parse common strings for names, etc

-- | 'alphanum' parses a string of letters and digits
alphanum :: ReadP String
alphanum = many1 (alpha <|> digit)

-- | 'varNameStr parses a variable name, which consists of a lowercase letter
-- followed by zero or more 'identchar's
varNameStr :: ReadP String
varNameStr = do c    <- lowercase
                rest <- Text.ParserCombinators.ReadP.many $ identchar
                return $ c : rest

-- | 'typeNameStr' parses a type name as a String. A type name must start with
-- an uppercase character followed by zero or more 'identchar's
typeNameStr :: ReadP String
typeNameStr = do c    <- uppercase
                 rest <- Text.ParserCombinators.ReadP.many $ identchar
                 return $ c : rest

-- | 'typeParamStr'
typeParamStr :: ReadP String
typeParamStr = do c  <- lowercase
                  cs <- many1 $ lowercase <|> digit
                  return $ c : cs

-- | 'commaSepList1' parses a comma separated list with at least one value
commaSepList :: ReadP a -> ReadP [a]
commaSepList p = sepBy p (padded $ char ',')

-- | 'commaSepList1' parses a comma separated list with at least one value
commaSepList1 :: ReadP a -> ReadP [a]
commaSepList1 p = sepBy1 p (padded $ char ',')

-- | 'spaceSepList' parses a (possibly empty) space separated list
spaceSepList :: ReadP a -> ReadP [a]
spaceSepList p = sepBy p (Text.ParserCombinators.ReadP.many1 $ satisfy isSpace)

-- | 'spaceSepList1' parses a (possibly empty) space separated list
spaceSepList1 :: ReadP a -> ReadP [a]
spaceSepList1 p = sepBy p (Text.ParserCombinators.ReadP.many1 $ satisfy isSpace)


