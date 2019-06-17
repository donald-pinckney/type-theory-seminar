module SimplyTyped.Parse
  ( parse
  , parseType
  ) where

import Text.ParserCombinators.ReadP
import Control.Applicative
import SimplyTyped.Syntax

{- Parsing -}

parens = between (char '(') (char ')')

term :: ReadP Term
term = do skipSpaces
          var <|> appl <|> abst <|> parens term

uppercase :: ReadP Char
uppercase = choice (map char ['A'..'Z'])

lowercase :: ReadP Char
lowercase = choice (map char ['a'..'z'])

digit :: ReadP Char
digit = choice (map char ['0'..'9'])

char_or_under :: ReadP Char
char_or_under = choice (Prelude.map char $ ('_' : ['a' .. 'z']))

varName :: ReadP String
varName = do c <- char_or_under
             rest <- Text.ParserCombinators.ReadP.many $ digit <|> char_or_under
             return $ c : rest

varType :: ReadP Type
varType = do c <- uppercase
             cs <- Text.ParserCombinators.ReadP.many $ uppercase <|> lowercase
             return $ TVar (c : cs)

subType :: ReadP Type
subType = do skipSpaces
             l <- varType <|> parens atype
             skipSpaces
             return l

atype :: ReadP Type
atype = do tpList <- subType `sepBy1` (string "->")
           case reverse tpList of
             [] -> error $ "parse error: Empty type found"
             h : t -> return $ foldl (\tp1 tp2 -> TArrow tp2 tp1) h t

parseType :: String -> Type
parseType s = let parses = filter (null . snd) ((readP_to_S atype) s) in
                  case parses of
                    [] -> error $ "parse error: Could not parse " ++ s
                    _  -> fst (last parses)

var :: ReadP Term
var = do nm <- varName
         return $ Var nm

abst :: ReadP Term
abst = do skipSpaces
          ((char 'λ') <|> (char '\\'))
          skipSpaces
          nm <- varName
          skipSpaces
          char ':'
          skipSpaces
          tp <- atype
          skipSpaces
          char '.'
          skipSpaces
          body <- term
          return $ Lambda (Decl nm tp) body

_appl :: [Term] -> Term
_appl [] = error "Parse error"
_appl (t : t' : ts) = _appl ((Appl t t') : ts)
_appl (t : []) = t

appl :: ReadP Term
appl = do t  <- varLambda
          ts <- many1 varLambda
          return $ _appl (t : ts)
            where varLambda = do t <- var <|> abst <|> parens term
                                 skipSpaces
                                 return t

parse :: String -> Term
parse s = let parses = (readP_to_S term) s in
              case parses of
                (p : _) -> fst (last parses)
                _       -> error "parse error"
