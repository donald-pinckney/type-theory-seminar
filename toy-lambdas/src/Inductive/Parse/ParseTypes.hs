module Inductive.Parse.ParseTypes
  ( makeParser
  , parseType
  , parseTypeDef
  , typeName
  , typeNameStr
  , varNameStr
  , typeProd
  , fnType
  , typeLit
  , typeDef
  ) where

import GHC.Unicode ( isSpace )
import Text.ParserCombinators.ReadP
import Control.Applicative
import Inductive.Syntax.Types
import Inductive.Parse.ParseUtil

-- -----------------------------------------------------------------------------
-- Top level parsing functions

-- | Parse a type, returning a 'Just tp' on success and a 'Nothing' on failure.
parseType :: String -> Maybe Type
parseType = makeParser typeLit

-- | Parse a type definition, returning a 'Just tpdef' on success and a
-- 'Nothing' on failure
parseTypeDef :: String -> Maybe TypeDef
parseTypeDef = makeParser typeDef

-- -----------------------------------------------------------------------------
-- Parse Types

-- | 'typeName' parses a 'Type' by reading a string and applying the 'TypeName'
-- value constructor
typeName :: ReadP Type
typeName = do nm <- typeNameStr
              return $ TypeName nm

-- | 'typeProd' parses a product type
typeProd :: ReadP Type
typeProd = do t <- (typeName <|> fnType)
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
typeLit = typeName <|> typeProd <|> fnType

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


