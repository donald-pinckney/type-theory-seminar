module Untyped 
  ( Term (..)
  , exec
  , pprint
  , betaReduce
  , normal
  , parse
  ) where

import Text.ParserCombinators.ReadP
import Data.Set
import Control.Applicative
import UnitTests


-- |Our grammar: a Term consists of variables, function abstraction, and
-- function application.
data Term = Var  String
          | Abst String Term
          | Appl Term   Term
          deriving (Show, Eq)

{- Semantics -}

-- | Return the set of free variables
fv :: Term -> Set String
fv (Var n) = singleton n
fv (Abst n t) = difference (fv t) (singleton n)
fv (Appl l r) = union (fv l) (fv r)

-- |Return the set of binding variables in a term
bv :: Term -> Set String
bv (Var x) = Data.Set.empty
bv (Abst x t) = union (bv t) (singleton x)
bv (Appl l r) = union (bv l) (bv r)

-- | Rename x to y in term
rename :: String -> String -> Term -> Term
rename x y term =
  case term of Var a -> if a == x then Var y else term
               Abst a t -> if a == x then term else Abst a (rename x y t)
               Appl l r -> Appl (rename x y l) (rename x y r)

-- | Generate a new name distinct from the set of names in @ns@
new_name :: Set String -> String
new_name ns = head (Prelude.filter (\x -> notMember x ns) ["$" ++ (show i) | i <- [0..]])

-- | If @n@ is not contained in @ns@, return it. Otherwise, generate a new name
-- distinct from those contained in @ns@ and return it.
default_or_new_name :: String -> Set String -> String
default_or_new_name n ns = if member n ns then new_name ns else n

-- | Perform substitution on a term, replacing all free instances of @Var x@
-- with term @new@
substitute :: String -> Term -> Term -> Term
substitute x new (Var y) = if x == y then new else (Var y)
substitute x new (Appl p q) = Appl (substitute x new p) (substitute x new q)
substitute x new (Abst y p) = let y' = default_or_new_name y (fv new)
                                  p' = rename y y' p
                              in Abst y' (substitute x new p')

-- | Perform one step of beta reduction. We choose an order of evaluation
-- application: namely, that we have @Appl l r@, we first check if @l@ is an
-- abstraction. If so, we perform the application. Otherwise, if @l@ isn't in
-- normal form, we perform one step of reduction on @l@. If it _is_ in normal
-- form we check if @r@ is normal, and if not perform one step of beta reduction
-- on it. If both @l@ and @r@ are normal and @l@ is not an abstraction we throw
-- an error.
-- TODO: This should maybe be replaced with a @Maybe Term@
betaReduce :: Term -> Term
betaReduce (Abst x b) = Abst x (betaReduce b)
betaReduce (Appl l r) =
  case l of Abst x b -> substitute x r b
            _ -> if not (normal l) then Appl (betaReduce l) r
                                   else if not (normal r)
                                         then Appl l (betaReduce r)
                                         else error $ (pprint_ (Appl l r)) ++ " is in normal form"
betaReduce x = if normal x then error $ (pprint_ x) ++ " is in normal form"
                           else error $ (pprint_ x) ++ " is not in normal form but no reduction exists"

-- | Test if a term is normal
normal :: Term -> Bool
normal (Var _) = True
normal (Abst x b) = normal b
normal (Appl l r) = case l of Abst _ _ -> False
                              _ -> normal l && normal r

-- | Apply beta reductions until the resulting term is normal.
exec :: Term -> Term
exec t = if normal t then t else exec (betaReduce t)

{- Parsing -}

term :: ReadP Term
term = do skipSpaces
          var <|> abst <|> appl <|> between (char '(') (char ')') term

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

{- Printing -}

pprint_ :: Term -> String
pprint_ (Var n) = n
pprint_ (Abst n t) = "λ" ++ (pprint_ (Var n)) ++ " . " ++ (pprint_ t)
pprint_ (Appl l r) = "(" ++ (pprint_ l) ++ " " ++ (pprint_ r) ++ ")"

pprint :: Term -> IO ()
pprint = putStrLn . pprint_

pprint' :: Maybe Term -> IO ()
pprint' (Just t) = pprint t
pprint' Nothing = putStrLn "parse error"
