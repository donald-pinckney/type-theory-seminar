module SimplyTyped.Semantics
  ( substitute
  , betaReduce
  , normal
  , exec
  , check
  ) where

import SimplyTyped.Syntax
import SimplyTyped.Print


{- Semantics -}

-- | Perform substitution on a term, replacing all free instances of @Var x@
-- with term @new@
substitute :: String -> Term -> Term -> Term
substitute x new (Var y) = if x == y then new else (Var y)
substitute x new (Appl p q) = Appl (substitute x new p) (substitute x new q)
substitute x new (Lambda y p) = if (name y) == x then (Lambda y p)
                                else (Lambda y (substitute x new p))

-- | Perform one step of beta reduction. We choose an order of evaluation
-- application: namely, that we have @Appl l r@, we first check if @l@ is an
-- abstraction. If so, we perform the application. Otherwise, if @l@ isn't in
-- normal form, we perform one step of reduction on @l@. If it _is_ in normal
-- form we check if @r@ is normal, and if not perform one step of beta reduction
-- on it. If both @l@ and @r@ are normal and @l@ is not an abstraction we throw
-- an error.
-- TODO: This should maybe be replaced with a @Maybe Term@
betaReduce :: Term -> Term
betaReduce (Lambda x b) = Lambda x (betaReduce b)
betaReduce (Appl l r) =
  case l of Lambda x b -> substitute (name x) r b
            _ -> if not (normal l) then Appl (betaReduce l) r
                                   else if not (normal r)
                                         then Appl l (betaReduce r)
                                         else error $ (pprint_ (Appl l r)) ++ " is in normal form"
betaReduce x = if normal x then error $ (pprint_ x) ++ " is in normal form"
                           else error $ (pprint_ x) ++ " is not in normal form but no reduction exists"

-- | Test if a term is normal
normal :: Term -> Bool
normal (Var _) = True
normal (Lambda d b) = normal b
normal (Appl l r) = case l of Lambda _ _ -> False
                              _ -> normal l && normal r

-- | Apply beta reductions until the resulting term is normal.
exec :: Term -> Term
exec t = if normal t then t else exec (betaReduce t)

{- Type Checking -}

-- | Given a typing environment, type check the program. If type checking
-- succeeds, return @Right tp@, where @tp@ is the type of the program. Otherwise,
-- return @Left err_msg@, where @err_msg@ is a @String@ containing an error
-- message explaining why type checking failed.
check :: Context -> Term -> Either String Type
check ctx (Var x)            =
  case ctxLookup ctx x of
    Nothing -> Left $ "Context doesn't contain a declaration for " ++ x
    Just t  -> Right t
check ctx (Lambda decl body) = (check (ctxInsert ctx decl) body) >>= (\t -> Right $ TArrow (tp decl) t)
check ctx (Appl fn arg)      =
  case (check ctx fn, check ctx arg) of
    (Right (TArrow dom cod), Right argTp) | dom == argTp -> Right cod
                                          | otherwise -> Left "Function types must be arrow types"
    (Left m, _) -> Left m
    (_, Left m) -> Left m
