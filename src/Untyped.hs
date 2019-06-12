module Untyped () where

import Text.ParserCombinators.ReadP
import Data.Set
import Control.Applicative
import Tests

{- Semantics -}

-- free vars
fv :: Term -> Set String
fv (Var n) = singleton n
fv (Abst n t) = difference (fv t) (singleton n)
fv (Appl l r) = union (fv l) (fv r)

-- binding variables
bv :: Term -> Set String
bv (Var x) = Data.Set.empty
bv (Abst x t) = union (bv t) (singleton x)
bv (Appl l r) = union (bv l) (bv r)

-- rename x to y in term
rename :: String -> String -> Term -> Term
rename x y term =
  case term of Var a -> if a == x then Var y else term
               Abst a t -> if a == x then term else Abst a (rename x y t)
               Appl l r -> Appl (rename x y l) (rename x y r)

new_name :: Set String -> String
new_name ns = head (Prelude.filter (\x -> notMember x ns) ["$" ++ (show i) | i <- [0..]])

default_or_new_name :: String -> Set String -> String
default_or_new_name n ns = if member n ns then new_name ns else n

term :: ReadP Term
term = do skipSpaces
          var <|> abst <|> appl <|> between (char '(') (char ')') term

substitute :: String -> Term -> Term -> Term
substitute x new (Var y) = if x == y then new else (Var y)
substitute x new (Appl p q) = Appl (substitute x new p) (substitute x new q)
substitute x new (Abst y p) = let y' = default_or_new_name y (fv new)
                                  p' = rename y y' p
                              in Abst y' (substitute x new p')

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

normal :: Term -> Bool
normal (Var _) = True
normal (Abst x b) = normal b
normal (Appl l r) = case l of Abst _ _ -> False
                              _ -> normal l && normal r


{- Parsing -}

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

data Term = Var  String
          | Abst String Term
          | Appl Term   Term
          deriving (Show, Eq)


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


{- Tests -}

x = Var "x"
y = Var "y"
z = Var "z"
a = Var "a"
b = Var "b"
c = Var "c"
d = Var "d"
id_ = Abst "x" x
id_id = Appl id_ id_
idy = Abst "y" y

parseTests = [ Test x                              (parse "x")             "parsing a varable"
             , Test y                              (parse "y")             "parsing a variable"
             , Test (Appl x y)                     (parse "x y")           "parsing an application"
             , Test (Appl (Appl x x) x)            (parse "x x x")         "application should be left associative"
             , Test (Appl (Appl (Appl a b) c) d)   (parse "a b c d")       "application should be left associative"
             , Test (Abst "x" (Appl (Appl x x) x)) (parse "\\ x . x x x ") "abstraction should bind looser than application"
             ]

normalTests = [ Test True  (normal x)              "Vars are in normal form"
              , Test True  (normal $ Appl x y)     "Application of two vars is normal"
              , Test False (normal $ Appl id_ y)    "Application of abstraction is not normal"
              , Test False (normal $ id_id)        "Application of abstraction is not normal"
              , Test True  (normal $ Appl x id_)    "Application of abstraction is not normal"
              , Test False (normal $ Appl x id_id) "Application with non-normal rhs is not normal"
              , Test False (normal $ Appl id_id x) "Application with non-normal lhs is not normal"
              ] where

reductionTests = [ Test x     (betaReduce (Appl id_ x))      "`(λ x . x) x` should reduce to x"
                 , Test id_id (betaReduce (Appl id_ id_id))  "`(λ x . x) ((λ x . x) (λ x . x))` should reduce to `(λ x . x) (λ x . x)`"
                 , Test id_id (betaReduce (Appl idy id_id))  "`(λ y . y) ((λ x . x) (λ x . x))` should reduce to `(λ x . x) (λ x . x)`"
                 , Test (Appl x x) (betaReduce (Appl x (Appl id_ x)))  "`λ x . (λ x . x) x`  should reduce to `λ x . x`"
                 ]


