module DependentlyTyped.Print
  ( pprint
  , pprint_
  , pprint_tp_
  ) where

import DependentlyTyped.Syntax

{- Printing -}

pprint_stp_ :: SuperType -> String
pprint_stp_ S = "*"
pprint_stp_ (SArrow S stp2) = "* -> " ++ (pprint_stp_ stp2)
pprint_stp_ (SArrow stp1 stp2) = "(" ++ (pprint_stp_ stp1) ++ ") -> " ++ (pprint_stp_ stp2)

pprint_tp_constr_ :: TypeConstr -> String
pprint_tp_constr_ (TVar nm) = nm
pprint_tp_constr_ (TArrow (TVar nm) tp2) = nm ++ " -> " ++ (pprint_tp_constr_ tp2)
pprint_tp_constr_ (TArrow tp1 tp2) = "(" ++ (pprint_tp_constr_ tp1) ++ ") -> " ++ (pprint_tp_constr_ tp2)
pprint_tp_constr_ (Pi (Decl nm tp1) tp2) = "Π" ++ nm ++ ":" ++ (pprint_tp_ tp1) ++ " . " ++ (pprint_tp_constr_ tp2)

pprint_tp_ :: Type -> String
pprint_tp_ (TConstr constr) = pprint_tp_constr_ constr
pprint_tp_ (SType stp) = pprint_stp_ stp
pprint_tp_ SSType = "□"

pprint_ :: Term -> String
pprint_ (Var n) = n
pprint_ (Lambda (Decl nm tp) t) = "λ" ++ nm ++ ":" ++ (pprint_tp_ tp) ++ " . " ++ (pprint_ t)
pprint_ (Appl l r) = "(" ++ (pprint_ l) ++ " " ++ (pprint_ r) ++ ")"
pprint_ (TTerm tp) = pprint_tp_ tp

pprint :: Term -> IO ()
pprint = putStrLn . pprint_

pprint' :: Maybe Term -> IO ()
pprint' (Just t) = pprint t
pprint' Nothing = putStrLn "parse error"
