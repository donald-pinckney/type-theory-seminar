module Inductive.Parse.ParseExpr
  (
  ) where

import GHC.Unicode ( isSpace )
import Text.ParserCombinators.ReadP
import Control.Applicative
import Inductive.Syntax.Expr
import Inductive.Parse.ParseUtil

intLit = many1 digit
