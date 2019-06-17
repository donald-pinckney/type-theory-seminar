module SimplyTyped.Syntax
  ( Term (..)
  , Type (..)
  , Decl (..)
  , Context
  , checkContextInvariant
  , ctxDomain
  , ctxLookup
  , ctxInsert
  ) where

import Data.Set (Set, notMember, insert, empty, singleton, union)
import Data.Map.Strict (Map)
import Data.List (sort)


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
