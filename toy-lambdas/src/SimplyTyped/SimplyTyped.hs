module SimplyTyped.SimplyTyped
  ( substitute
  , betaReduce
  , normal
  , exec
  , check
  , Term (..)
  , Type (..)
  , Decl (..)
  , Context
  , checkContextInvariant
  , ctxDomain
  , ctxLookup
  , ctxInsert
  ) where

import Data.Set (Set, notMember, insert, empty, singleton, union, member, difference)
import Data.Map.Strict (Map)
import Data.List (sort)

{- Syntax -}

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

{- Semantics -}

-- | Return the set of free variables
fv :: Term -> Set String
fv (Var n) = singleton n
fv (Lambda n t) = difference (fv t) (singleton $ name n)
fv (Appl l r) = union (fv l) (fv r)

-- | Rename x to y in term
rename :: String -> String -> Term -> Term
rename x y term =
  case term of Var a -> if a == x then Var y else term
               Lambda a t -> if name a == x then term else Lambda a (rename x y t)
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
substitute x new (Lambda y p) = if (name y) == x then (Lambda y p)
                                else 
                                  let y_new_name = default_or_new_name (name y) (fv new)
                                      p' = rename (name y) y_new_name p
                                  in Lambda (Decl y_new_name (tp y)) (substitute x new p')
                                  -- (Lambda y (substitute x new p))

-- substitute :: String -> Term -> Term -> Term
-- substitute x new (Var y) = if x == y then new else (Var y)
-- substitute x new (Appl p q) = Appl (substitute x new p) (substitute x new q)
-- substitute x new (Abst y p) = let y' = default_or_new_name y (fv new)
--                                   p' = rename y y' p
--                               in Abst y' (substitute x new p')

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
                                         else error $ (show (Appl l r)) ++ " is in normal form"
betaReduce x = if normal x then error $ (show x) ++ " is in normal form"
                           else error $ (show x) ++ " is not in normal form but no reduction exists"

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
check ctx (Var x)            =
  case ctxLookup ctx x of
    Nothing -> Left $ "Context doesn't contain a declaration for " ++ x
    Just t  -> Right t
check ctx (Lambda decl body) = (check (ctxInsert ctx decl) body) >>= (\t -> Right $ TArrow (tp decl) t)
check ctx (Appl fn arg)      =
  case (check ctx fn, check ctx arg) of
    (Right (TArrow dom cod), Right argTp) | dom == argTp -> Right cod
                                          | otherwise -> Left "Function types must be arrow types"
    (Left m, _) -> Left m
    (_, Left m) -> Left m


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
