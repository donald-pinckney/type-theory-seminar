module ch2.Resolve

import ch2.AST
import ch2.Parse
import Debug.Error
import Result
import ParseUtils


public export
ResolveResult : Type
ResolveResult = Result AST.Term


resolveType : ParsedType -> Type'
resolveType (TypeVariable v) = VarType $ FreeType v
resolveType (TypeArrow a b) = Arrow (resolveType a) (resolveType b)



total
addVar : List String -> String -> Result (List String)
addVar vars x =
    if x `elem` vars then
        Left $ "Can not redefine variable: " ++ x
    else
        Right $ x :: vars


resolveMain : List String -> ParsedTerm -> ResolveResult
resolveMain vars (Variable x) =
    case x `elemIndex` vars of
        Just n => Right $ Var (Bound n)
        Nothing => Right $ Var (Free x)
        -- Nothing => Left $ "Could not resolve variable: " ++ x

resolveMain vars (App x y) = do
    x' <- resolveMain vars x
    y' <- resolveMain vars y
    pure $ App x' y'

resolveMain vars (Lambda [] body) = Left $ "Invalid parse, lambda term must have at least 1 parameter."
resolveMain vars (Lambda ((v, t) :: []) body) = do
    vars' <- addVar vars v
    body' <- resolveMain vars' body
    pure $ AST.Lambda (resolveType t) body'

resolveMain vars (Lambda (x :: (y :: xs)) body) = resolveMain vars (Lambda [x] (Lambda (y :: xs) body))

export
resolve : ParsedTerm -> ResolveResult
resolve = resolveMain []

export
parseAndResolve_unpacked : SourceString -> ResolveResult
parseAndResolve_unpacked str = do
    p <- parse_unpacked str
    resolve p

export
parseAndResolve : String -> ResolveResult
parseAndResolve str = do
    p <- parse str
    resolve p



%language ElabReflection

export
parseAndResolve_force : String -> AST.Term
parseAndResolve_force x = case parseAndResolve x of
    (Left l) => error $ "Parsing Error: " ++ l
    (Right r) => r
