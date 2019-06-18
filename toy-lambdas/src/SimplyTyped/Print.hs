module SimplyTyped.Print
  ( pprint
  , pprint_
  , pprint_tp_
  ) where

import SimplyTyped.Syntax


{- Printing -}

pprint_ :: Term -> String
pprint_ (Var n) = n
pprint_ (Lambda (Decl nm tp) t) = "λ" ++ nm ++ ":" ++ (pprint_tp_ tp) ++ " . " ++ (pprint_ t)
pprint_ (Appl l r) = "(" ++ (pprint_ l) ++ " " ++ (pprint_ r) ++ ")"

pprint_tp_ :: Type -> String
pprint_tp_ (TVar nm) = nm
pprint_tp_ (TArrow l r) =
  case l of
    TVar nm' -> (pprint_tp_ l) ++ " -> " ++ (pprint_tp_ r)
    TArrow l' r' -> "(" ++ (pprint_tp_ l) ++ ") -> " ++ (pprint_tp_ r)

pprint :: Term -> IO ()
pprint = putStrLn . pprint_

pprint' :: Maybe Term -> IO ()
pprint' (Just t) = pprint t
pprint' Nothing = putStrLn "parse error"
