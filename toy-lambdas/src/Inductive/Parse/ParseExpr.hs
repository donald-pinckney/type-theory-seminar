module Inductive.Parse.ParseExpr
  ( parseExpr
  ) where

import GHC.Unicode ( isSpace )
import Text.ParserCombinators.ReadP
import Control.Applicative
import Inductive.Syntax.Expr
import Inductive.Parse.ParseUtil
import Text.Read

intLit :: ReadP Int
intLit = do
  dig <- many1 digit
  return $ read dig

trueLit :: ReadP Bool
trueLit = do
  string "true"
  return $ True 

falseLit :: ReadP Bool
falseLit = do
  string "false"
  return $ False 

boolLit = trueLit <|> falseLit

-- | Parse an expression, returning a 'Just exp' on success and a 'Nothing' on failure.
parseExpr :: String -> Maybe Expr
parseExpr = makeParser expr

simpleExpr :: ReadP Expr
simpleExpr = exprITE
  <|> exprLet
  <|> exprIntLiteral
  <|> exprBoolLiteral
  <|> exprVar
  <|> Inductive.Parse.ParseUtil.parens expr

expr :: ReadP Expr
expr = exprPossibleFuncApp

exprPossibleFuncApp :: ReadP Expr
exprPossibleFuncApp = do
  exprs <- funcAppList
  case buildFuncApp exprs of 
    Nothing -> Text.ParserCombinators.ReadP.pfail
    Just e -> return $ e
  where
    buildFuncApp :: [Expr] -> Maybe Expr
    buildFuncApp [] = Nothing
    buildFuncApp [e] = Just e 
    buildFuncApp (f : a : rest) = buildFuncApp (ExprApp f a : rest)

funcAppList :: ReadP [Expr]
funcAppList = spaceSepList1 simpleExpr

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
  return $ ExprLit $ LitInt n

exprBoolLiteral :: ReadP Expr
exprBoolLiteral = do
  b <- boolLit
  return $ ExprLit $ LitBool b