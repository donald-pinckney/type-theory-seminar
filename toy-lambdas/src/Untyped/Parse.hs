module Untyped.Parse
  ( parse
  ) where

import Text.ParserCombinators.ReadP
import Untyped.Untyped
import Control.Applicative


{- Parsing -}

term :: ReadP Term
term = do skipSpaces
          var <|> appl <|> abst <|> between (char '(') (char ')') term

char_or_under :: ReadP Char
char_or_under = choice (Prelude.map char $ ('_' : ['a' .. 'z']))

name :: ReadP String
name = do c <- char_or_under
          rest <- Text.ParserCombinators.ReadP.many $ choice (Prelude.map char ['0'..'9']) <|> char_or_under
          return $ c : rest

var :: ReadP Term
var = do nm <- name
         return $ Var nm

abst :: ReadP Term
abst = do skipSpaces
          ((char 'λ') <|> (char '\\'))
          skipSpaces
          nm <- name
          skipSpaces
          char '.'
          skipSpaces
          body <- term
          return $ Abst nm body

parens = between (char '(') (char ')')

_appl :: [Term] -> Term
_appl [] = error "Parse error"
_appl (t : t' : ts) = _appl ((Appl t t') : ts)
_appl (t : []) = t

appl :: ReadP Term
appl = do t  <- varAbst
          ts <- many1 varAbst
          return $ _appl (t : ts)
            where varAbst = do t <- var <|> abst <|> parens term
                               skipSpaces
                               return t

parse s = let parses = (readP_to_S term) s in
              case parses of
                (p : _) -> fst (last parses)
                _ -> error "parse error"
