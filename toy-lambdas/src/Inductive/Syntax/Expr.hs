module Inductive.Syntax.Expr
  ( Value(..)
  , Expr(..)
  ) where

-- | 'Value' represents things in normal form
data Value
  -- | 'ValueInt' represents an integer value
  = ValueInt Int
  -- | 'ValueBoolean' represents a boolean value
  | ValueBool Bool
  deriving (Eq, Show)

-- | 'Expr' represents an expression in the object language
data Expr
  -- | 'ExprLet' constructs a let binding
  = ExprLet String Expr Expr
  -- | 'ExprITE' constructs if e1 then e2 else e3
  | ExprITE Expr Expr Expr
  -- | 'ExprVar' constructs a variable
  | ExprVar String
  -- | 'ExprValue' constructs a base value
  | ExprValue Value
  -- | 'ExprApp' constructs a function application
  | ExprApp Expr Expr
  deriving (Eq, Show)
