module Inductive.Syntax.Expr
  ( Lit(..)
  , Expr(..)
  ) where

-- | 'Lit' represents literals
data Lit
  -- | 'LitInt' represents an integer literal
  = LitInt Int
  -- | 'LitBool' represents a boolean literal
  | LitBool Bool
  deriving (Eq, Show)

-- | 'Expr' represents an expression in the object language
data Expr
  -- | 'ExprLet' constructs a let binding
  = ExprLet String Expr Expr
  -- | 'ExprITE' constructs if e1 then e2 else e3
  | ExprITE Expr Expr Expr
  -- | 'ExprVar' constructs a variable
  | ExprVar String
  -- | 'ExprLit' constructs a literal value
  | ExprLit Lit
  -- | 'ExprApp' constructs a function application
  | ExprApp Expr Expr
  deriving (Eq, Show)
