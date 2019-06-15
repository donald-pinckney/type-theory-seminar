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
  , substitute
  , betaReduce
  , exec
  , check
  ) where

import Text.ParserCombinators.ReadP
import Data.Set (Set, notMember, insert, empty, singleton, union)
import Data.Map.Strict (Map)
import Data.List (sort)
import Control.Applicative

data Type = TVar String
          | TArrow Type Type
          | Unknown
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

ctxInsert :: Context -> Decl -> Context
ctxInsert [] decl = return decl
ctxInsert (d:ds) decl = if (name d) == (name decl) then decl:ds else d : (ctxInsert ds decl)

{- Semantics -}

-- | Perform substitution on a term, replacing all free instances of @Var x@
-- with term @new@
substitute :: String -> Term -> Term -> Term
substitute x new (Var y) = if x == y then new else (Var y)
substitute x new (Appl p q) = Appl (substitute x new p) (substitute x new q)
substitute x new (Lambda y p) = if (name y) == x then (Lambda y p)
                                else (Lambda y (substitute x new p))

-- | Perform one step of beta reduction. We choose an order of evaluation
-- application: namely, that we have @Appl l r@, we first check if @l@ is an
-- abstraction. If so, we perform the application. Otherwise, if @l@ isn't in
-- normal form, we perform one step of reduction on @l@. If it _is_ in normal
-- form we check if @r@ is normal, and if not perform one step of beta reduction
-- on it. If both @l@ and @r@ are normal and @l@ is not an abstraction we throw
-- an error.
-- TODO: This should maybe be replaced with a @Maybe Term@
betaReduce :: Term -> Term
betaReduce (Lambda x b) = Lambda x (betaReduce b)
betaReduce (Appl l r) =
  case l of Lambda x b -> substitute (name x) r b
            _ -> if not (normal l) then Appl (betaReduce l) r
                                   else if not (normal r)
                                         then Appl l (betaReduce r)
                                         else error $ (pprint_ (Appl l r)) ++ " is in normal form"
betaReduce x = if normal x then error $ (pprint_ x) ++ " is in normal form"
                           else error $ (pprint_ x) ++ " is not in normal form but no reduction exists"

-- | Test if a term is normal
normal :: Term -> Bool
normal (Var _) = True
normal (Lambda d b) = normal b
normal (Appl l r) = case l of Lambda _ _ -> False
                              _ -> normal l && normal r

-- | Apply beta reductions until the resulting term is normal.
exec :: Term -> Term
exec t = if normal t then t else exec (betaReduce t)

{- Type Checking -}

-- | Given a typing environment, type check the program. If type checking
-- succeeds, return @Right tp@, where @tp@ is the type of the program. Otherwise,
-- return @Left err_msg@, where @err_msg@ is a @String@ containing an error
-- message explaining why type checking failed.
check :: Context -> Term -> Either String Type
check ctx (Var x) = case ctxLookup ctx x of
                         Nothing -> Left $ "Context doesn't contain a declaration for " ++ x
                         Just t  -> Right t
check ctx (Lambda decl body) = (check (ctxInsert ctx decl) body) >>= (\t -> Right $ TArrow (tp decl) t)

check ctx (Appl fn arg)      =
  case (check ctx fn, check ctx arg) of
    (Right (TArrow dom cod), Right argTp) ->
      if dom == argTp
         then Right cod
         else Left $ "Argument doesn't match function type"
    (Right (TArrow dom cod), Left m) -> Left m
    (Right _, _) -> Left "Function types must be arrow types"
    (Left m, _) -> Left m

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

