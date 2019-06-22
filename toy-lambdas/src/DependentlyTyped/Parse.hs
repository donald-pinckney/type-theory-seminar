module DependentlyTyped.Parse
  ( parse
  , parseType
  ) where

import Text.ParserCombinators.ReadP
import Control.Applicative
import DependentlyTyped.Syntax

{- Parsing -}

{- Symbols -}
lambdaSym = (char 'λ') <|> (char '\\')
piSym = (string "Π") <|> (string "PI")
sSym = char '*'
ssSym = (char '□') <|> (char 'U')

uppercase :: ReadP Char
uppercase = choice (map char ['A'..'Z'])

lowercase :: ReadP Char
lowercase = choice (map char ['a'..'z'])

digit :: ReadP Char
digit = choice (map char ['0'..'9'])

char_or_under :: ReadP Char
char_or_under = (char '_') <|> uppercase <|> lowercase

varName :: ReadP String
varName = do c <- char_or_under
             rest <- Text.ParserCombinators.ReadP.many $ digit <|> char_or_under
             return $ c : rest

parens = between (char '(') (char ')')

{- Parses the super super type -}

superSuperType :: ReadP Type
superSuperType = do skipSpaces
                    ssSym
                    skipSpaces
                    return SSType

{- Parses super type -}

atomicSuperType :: ReadP SuperType
atomicSuperType = do skipSpaces
                     sSym
                     skipSpaces
                     return S

subSuperType :: ReadP SuperType
subSuperType = do skipSpaces
                  l <- atomicSuperType <|> parens superType
                  skipSpaces
                  return l

superType :: ReadP SuperType
superType = do tpList <- subSuperType `sepBy1` (string "->")
               case reverse tpList of
                 [] -> error $ "parse error: Empty super type found"
                 h : t -> return $ foldl (\tp1 tp2 -> SArrow tp2 tp1) h t

{- Parses type constructors -}

varType :: ReadP TypeConstr
varType = do nm <- varName
             return $ TVar nm

piType :: ReadP TypeConstr
piType = do skipSpaces
            piSym
            skipSpaces
            nm <- varName
            skipSpaces
            char ':'
            skipSpaces
            tp <- superType
            skipSpaces
            char '.'
            skipSpaces
            body <- typeConstr
            return $ Pi (Decl nm (SType tp)) body

subConstr :: ReadP TypeConstr
subConstr = do skipSpaces
               l <- varType <|> parens typeConstr
               skipSpaces
               return l

typeConstr :: ReadP TypeConstr
typeConstr = do tpList <- subConstr `sepBy1` (string "->")
                case reverse tpList of
                  [] -> error $ "parse error: Empty type found"
                  h : t -> return $ foldl (\tp1 tp2 -> TArrow tp2 tp1) h t

atype :: ReadP Type
atype = do tconstr <- typeConstr
           return $ TConstr tconstr
        <|>
        do stype <- superType
           return $ SType stype
        <|>
        superSuperType

parseType ::  String -> Type
parseType s = let parses = filter (null . snd) ((readP_to_S atype) s) in
                  case parses of
                    [] -> error $ "parse error: Could not parse " ++ s
                    _  -> fst (last parses)

{- Parses terms -}

var :: ReadP Term
var = do nm <- varName
         return $ Var nm

abst :: ReadP Term
abst = do skipSpaces
          lambdaSym
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
appl = do t <- varLambda
          ts <- many1 varLambda
          return $ _appl (t : ts)
            where varLambda = do t <- (var <|> abst <|> parens term) <++ tterm
                                 skipSpaces
                                 return t

tterm :: ReadP Term
tterm = do t <- atype
           return $ TTerm t

term :: ReadP Term
term = do skipSpaces
          t <- (var <|> appl <|> abst <|> parens term) <++ tterm
          skipSpaces
          return t

parse ::  String -> Term
parse s = let parses = filter (null . snd) ((readP_to_S term) s) in
                  case parses of
                    [] -> error $ "parse error: Could not parse " ++ s
                    _  -> fst (last parses)
