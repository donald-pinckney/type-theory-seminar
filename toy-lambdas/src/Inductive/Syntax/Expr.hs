module Inductive.Syntax.Expr
  ( Expr(..)
  ) where

-- | 'Expr' represents an expression in the object language
data Expr
  -- | 'ExprLet' constructs a let binding
  = ExprLet String Expr Expr
  -- | 'ExprITE' constructs if e1 then e2 else e3
  | ExprITE Expr Expr Expr
  -- | 'ExprVar' constructs a variable
  | ExprVar String
  -- | 'ExprIntLiteral' constructs an integer literal
  | ExprIntLiteral Int
  deriving (Eq, Show)
