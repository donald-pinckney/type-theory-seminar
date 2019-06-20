module Inductive.Parse.ParseTypes
  ( makeParser
  , parseType
  , parseTypeDef
  , typeName
  , typeNameStr
  , varNameStr
  , prodType
  , fnType
  , typeLit
  , typeDef
  ) where

import GHC.Unicode ( isSpace )
import Text.ParserCombinators.ReadP
import Control.Applicative
import Inductive.Syntax

-- -----------------------------------------------------------------------------
-- Top level parsing functions

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

-- | Parse a type, returning a 'Just tp' on success and a 'Nothing' on failure.
parseType :: String -> Maybe Type
parseType = makeParser typeLit

-- | Parse a type definition, returning a 'Just tpdef' on success and a
-- 'Nothing' on failure
parseTypeDef :: String -> Maybe TypeDef
parseTypeDef = makeParser typeDef

-- -----------------------------------------------------------------------------
-- Some helper parsers

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
commaSepList1 :: ReadP a -> ReadP [a]
commaSepList1 p = sepBy1 p (padded $ char ',')

-- | 'spaceSepList' parses a (possibly empty) space separated list
spaceSepList :: ReadP a -> ReadP [a]
spaceSepList p = sepBy p (Text.ParserCombinators.ReadP.many1 $ satisfy isSpace)

-- -----------------------------------------------------------------------------
-- Parse Types

-- | 'typeName' parses a 'Type' by reading a string and applying the 'TypeName'
-- value constructor
typeName :: ReadP Type
typeName = do nm <- typeNameStr
              return $ TypeName nm

-- | 'prodType' parses a product type
prodType :: ReadP Type
prodType = do t <- (typeName <|> fnType)
              (padded (char '*'))
              ts <- sepBy1 (typeName <|> fnType) (padded (char '*'))
              return $ ProdType (t : ts)

-- | 'fnType' parses a function type
fnType :: ReadP Type
fnType = do dom <- parens typeLit <|> typeName
            padded (string "->")
            cod <- typeLit
            return $ FnType dom cod

-- | 'typeLit' parses a 'Type', which is defined to be a type name, a product
-- type, or a function type.
typeLit :: ReadP Type
typeLit = typeName <|> prodType <|> fnType

-- | 'typeDef' parses a 'TypeDef'
typeDef :: ReadP TypeDef
typeDef =
  do padded (string "data")
     tName   <- padded typeNameStr
     tParams <- padded optTypeParams
     padded (char '=')
     tbody   <- typeDefBody
     return $ TypeDef tName tParams tbody where

       optTypeParams      = return [] <|> (padded $ string "::") >> commaSepList1 typeParamStr
       typeDefBody        = valConstructorBody <++ typeLitBody
       typeLitBody        = typeLit >>= return . TpDefLiteral
       valConstructorBody = valConstructorList >>= return . TpDefValConstr
       valConstructorList = sepBy1 valConstructor (padded vbar)
       valConstructor     = do tName  <- typeNameStr
                               skipSpaces
                               tpList <- spaceSepList (typeName <|> (parens typeLit))
                               return $  ValConstructor tName tpList


