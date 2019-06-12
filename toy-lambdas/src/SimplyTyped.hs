module SimplyTyped 
  (
  ) where

import Text.ParserCombinators.ReadP
import Data.Set
import Control.Applicative
import UnitTests

data Type = TVar String
          | TArrow Type Type
          deriving (Show, Eq)

data Decl = Decl { name :: String, tp :: Type }
            deriving (Show, Eq)

data Term = Var String
          | Lambda Decl
          | Appl Term Term
          deriving (Show, Eq)
