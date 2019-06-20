module Inductive.Parse
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

makeParser :: ReadP a -> String -> Maybe a
makeParser p s = let parses = (readP_to_S p) s in
                     case (filter (null . snd) parses) of
                       (p : _) -> Just $ (fst . last) parses
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

parens    = between (char '(') (char ')')
braces    = between (char '{') (char '}')
padded    = between skipSpaces skipSpaces
vbar      = (char '|')
uppercase = choice (map char ['A'..'Z'])
lowercase = choice (map char ['a'..'z'])
alpha     = uppercase <|> lowercase
digit     = choice (map char ['0'..'9'])

-- | parse a letter or a digit
alphanum :: ReadP String
alphanum = many1 (alpha <|> digit)

-- | 'identchar' parses an internal identifier character, which includes
-- letters, numbers, and underscores
identchar :: ReadP Char
identchar = (char '_') <|> alpha <|> digit

-- | 'varNameStr parses a variable name, which consists of a lowercase letter
-- followed by zero or more 'identchar's
varNameStr :: ReadP String
varNameStr = do c <- lowercase
                rest <- Text.ParserCombinators.ReadP.many $ identchar
                return $ c : rest

-- | 'typeNameStr' parses a type name as a String. A type name must start with
-- an uppercase character followed by zero or more 'identchar's
typeNameStr :: ReadP String
typeNameStr = do c <- uppercase
                 rest <- Text.ParserCombinators.ReadP.many $ identchar
                 return $ c : rest

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
typeDef = do padded (string "data")
             tName   <- padded typeNameStr
             tParams <- padded optTypeParams
             padded (char '=')
             tbody   <- typeDefBody
             return $ TypeDef tName tParams tbody

emptyTypeParams :: ReadP [TypeParam]
emptyTypeParams = do return []

optTypeParams :: ReadP [TypeParam]
optTypeParams = emptyTypeParams <|>
                do (padded $ string "::")
                   params <- sepBy1 (many1 lowercase) (padded (char ','))
                   return params

typeDefBody :: ReadP TypeDefBody
typeDefBody = valConstructorBody <++ typeLitBody

typeLitBody :: ReadP TypeDefBody
typeLitBody = do t <- typeLit
                 return $ TpDefLiteral t

valConstructorBody :: ReadP TypeDefBody
valConstructorBody = do cs <- valConstructorList
                        return $ TpDefValConstr cs
  where
    valConstructorList :: ReadP [ValConstructor]
    valConstructorList = sepBy1 valConstructor (padded vbar)
    valConstructor :: ReadP ValConstructor
    valConstructor = do tName  <- typeNameStr
                        skipSpaces
                        tpList <- sepBy (typeName <|> (parens typeLit)) (many1 (satisfy isSpace))
                        return $  ValConstructor tName tpList

