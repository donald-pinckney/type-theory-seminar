module Inductive.Parse.ParseExpr
  ( parseExpr
  ) where

import GHC.Unicode ( isSpace )
import Text.ParserCombinators.ReadP
import Control.Applicative
import Inductive.Syntax.Expr
import Inductive.Parse.ParseUtil

intLit = many1 digit



-- | Parse an expression, returning a 'Just exp' on success and a 'Nothing' on failure.
parseExpr :: String -> Maybe Expr
parseExpr = makeParser expr

expr :: ReadP Expr
expr = exprLet <|> exprITE <|> exprVar <|> exprIntLiteral

exprLet :: ReadP Expr
exprLet = do
  padded (string "let")
  name <- varNameStr
  padded (char '=')
  bindExpr <- expr
  padded (string "in")
  inExpr <- expr
  return $ ExprLet name bindExpr inExpr

exprITE :: ReadP Expr
exprITE = do
  padded (string "if")
  cond <- expr
  padded (string "then")
  thenBranch <- expr
  padded (string "else")
  elseBranch <- expr
  return $ ExprITE cond thenBranch elseBranch

exprVar :: ReadP Expr
exprVar = do
  v <- varNameStr
  return $ ExprVar v

exprIntLiteral :: ReadP Expr
exprIntLiteral = do
  n <- intLit
  return $ ExprValue $ ValueInt (read n)