module Inductive.Syntax
  (
  ) where

data TypeConstructor = TypeConstructor
  { name :: String
  , args :: [Type]
  , tp   :: Type
  }

data Type = IntType  Int
          | BoolType Bool
          | ProdType [Type]
          | SumType  [Type]
          | NamedADT
          deriving (Show, Eq)
