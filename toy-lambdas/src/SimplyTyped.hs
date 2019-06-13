module SimplyTyped
  (checkContextInvariant
  , Type (..)
  , Decl (..)
  , Context
  , Term (..)
  , parse
  , parseType
  , pprint
  , pprint_
  , pprint_tp_
  , check
  ) where

import Text.ParserCombinators.ReadP
import Data.Set (Set, notMember, insert, empty, singleton, union)
import Data.List (sort)
import Control.Applicative

data Type = TVar String
          | TArrow Type Type
          deriving (Show, Eq)

data Term = Var String
          | Lambda Decl Term
          | Appl Term Term
          deriving (Show, Eq)

-- | A @Decl@ (or _declaration_) is a statement with a variable as subject. A
-- _statement_ is of the form M : T, where M is a Term and T is a type
data Decl = Decl { name :: String, tp :: Type }
            deriving (Show, Eq)

-- | A @Context@ is a list of declarations with _different_ subjects. This isn't
-- enforced here, but instead should be enforced by an API
type Context = [Decl]

checkContextInvariant :: Context -> Bool
checkContextInvariant = ctxCompare . sort . ctxDomain

ctxCompare :: [String] -> Bool
ctxCompare (x : y : cs)
  | x == y = False
  | otherwise = ctxCompare (y : cs)
ctxCompare _ = True


ctxDomain :: Context -> [String]
ctxDomain = map name

-- | Recursively get all type variable names from a term
termToTVars :: Term -> Set String
termToTVars (Var x)               = Data.Set.empty
termToTVars (Lambda (Decl v t) b) = union (typeToTVars t) (termToTVars b)
termToTVars (Appl l r)            = union (termToTVars l) (termToTVars r)

-- | Recursively get all type variable names from a type
typeToTVars :: Type -> Set String
typeToTVars (TVar x)     = singleton x
typeToTVars (TArrow l r) = union (typeToTVars l) (typeToTVars r)

-- | Lookup a type associated with a variable in a @Context@
ctxLookup :: Context -> String -> Maybe Type
ctxLookup []   name = Nothing
ctxLookup ((Decl x tp):ds) name = if x == name then Just tp else ctxLookup ds name

{- Type Checking -}

-- | Given a context, type check the program. If type checking succeeds, return
-- @Just tp@, where @tp@ is the type of the program. Otherwise, return
-- @Nothing@, signifying that type checking failed.
--
-- TODO: The current setup is insufficient. We will need to build up some sort
-- of unification for variable names. For instance, consider the following
-- program:
-- > check (λ a:A . (λ b:B . b) a"
-- This applies (λ b:B . b) to variable a of type A. This _can_ type check, but
-- we need to unify types A and B.
check :: Context -> Term -> Maybe Type
check ctx (Var x)            = error "Not implemented"
check ctx (Lambda decl body) = error "Not implemented"
check ctx (Appl fn arg)      = error "Not implemented"

{- Parsing -}

term :: ReadP Term
term = do skipSpaces
          var <|> abst <|> appl <|> between (char '(') (char ')') term

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

arrowType :: ReadP Type
arrowType = do skipSpaces
               l <- varType <|> parens atype
               skipSpaces
               string "->"
               skipSpaces
               r <- atype
               skipSpaces
               return $ TArrow l r

atype :: ReadP Type
atype = arrowType <++ varType

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

parens = between (char '(') (char ')')

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

{- Printing -}

pprint_ :: Term -> String
pprint_ (Var n) = n
pprint_ (Lambda (Decl nm tp) t) = "λ" ++ nm ++ ":" ++ (pprint_tp_ tp) ++ " . " ++ (pprint_ t)
pprint_ (Appl l r) = "(" ++ (pprint_ l) ++ " " ++ (pprint_ r) ++ ")"

pprint_tp_ :: Type -> String
pprint_tp_ (TVar nm) = nm
pprint_tp_ (TArrow l r) =
  case l of
    TVar nm' -> (pprint_tp_ l) ++ " -> " ++ (pprint_tp_ r)
    TArrow l' r' -> "(" ++ (pprint_tp_ l) ++ ") -> " ++ (pprint_tp_ r)

pprint :: Term -> IO ()
pprint = putStrLn . pprint_

pprint' :: Maybe Term -> IO ()
pprint' (Just t) = pprint t
pprint' Nothing = putStrLn "parse error"

