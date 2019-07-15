module defs.Resolve

import defs.AST
import defs.CST
import defs.Parse
import defs.Identifier
import Result
import ParseUtils
import Data.Vect


public export
ResolveResult : Nat -> Nat -> Type
ResolveResult envLen contextLen = Result (ABook envLen contextLen)

public export
ResolveResultRoot : Type
ResolveResultRoot = ResolveResult Z Z


total
addToEnv : Vect n Identifier -> Vect m Identifier -> Identifier -> Result (Vect (S n) Identifier)
addToEnv env context x =
    if any (sameIdentifier x) env || any (sameIdentifier x) context then
        Left $ "Can not redefine '" ++ (text x) ++ "'"
    else
        Right $ x :: env

total
addToContext : Vect n Identifier -> Vect m Identifier -> Identifier -> Result (Vect (S m) Identifier)
addToContext env context x =
    if any (sameIdentifier x) env || any (sameIdentifier x) context then
        Left $ "Can not redefine '" ++ (text x) ++ "'"
    else
        Right $ x :: context

total
lookupId : Vect k Identifier -> Identifier -> Maybe (Fin k)
lookupId [] x = Nothing
lookupId (y :: xs) x =
    if x == y then
        Just FZ
    else
        FS <$> lookupId xs x


resolveVar : Vect envLen Identifier -> Vect contextLen Identifier -> Identifier -> Result (ResolvedIdentifier envLen contextLen)
resolveVar envDefs contextVars x =
    case lookupId envDefs x of
        (Just idx) => success $ Definition $ MkDeBruijnIdentifier idx x
        Nothing => case lookupId contextVars x of
            (Just idx) => success $ Context $ MkDeBruijnIdentifier idx x
            Nothing => error $ "Use of undeclared variable or definition: " ++ (show x)

resolveExpr : Nat -> Vect envLen Identifier -> Vect contextLen Identifier -> CExpr -> Result (AExpr envLen contextLen, Nat)
resolveExpr uniqueId envDefs contextVars CExprStar = success (AExprStar, uniqueId)
resolveExpr uniqueId envDefs contextVars CExprBox = success (AExprBox, uniqueId)
resolveExpr uniqueId envDefs contextVars CExprPostulate = success (AExprPostulate, uniqueId)
resolveExpr uniqueId envDefs contextVars (CExprApp x y) = do
    (x', uniqueId) <- resolveExpr uniqueId envDefs contextVars x
    (y', uniqueId) <- resolveExpr uniqueId envDefs contextVars y
    success (AExprApp x' y', uniqueId)
resolveExpr uniqueId envDefs contextVars (CExprArrow (Left leftT) rightT) = do
    let uniqueDeadId = MkIdentifier (unpackSource $ "__unique_" ++ show uniqueId)
    let uniqueId = S uniqueId
    extendedContext <- addToContext envDefs contextVars uniqueDeadId
    (leftResolvedT, uniqueId) <- resolveExpr uniqueId envDefs contextVars leftT
    (rightResolvedT, uniqueId) <- resolveExpr uniqueId envDefs extendedContext rightT
    success (AExprArrow (MkADecl leftResolvedT uniqueDeadId) rightResolvedT, uniqueId)
resolveExpr uniqueId envDefs contextVars (CExprArrow (Right (MkCDecl var type)) rightT) = do
    extendedContext <- addToContext envDefs contextVars var
    (leftResolvedT, uniqueId) <- resolveExpr uniqueId envDefs contextVars type
    (rightResolvedT, uniqueId) <- resolveExpr uniqueId envDefs extendedContext rightT
    success (AExprArrow (MkADecl leftResolvedT var) rightResolvedT, uniqueId)
resolveExpr uniqueId envDefs contextVars (CExprLambda [] x) = error "Invalid parse, lambda term must have at least 1 parameter."
resolveExpr uniqueId envDefs contextVars (CExprLambda ((MkCDecl var type) :: []) body) = do
    extendedContext <- addToContext envDefs contextVars var
    (typeResolved, uniqueId) <- resolveExpr uniqueId envDefs contextVars type
    (bodyResolved, uniqueId) <- resolveExpr uniqueId envDefs extendedContext body
    success (AExprLambda (MkADecl typeResolved var) bodyResolved, uniqueId)
resolveExpr uniqueId envDefs contextVars (CExprLambda (v :: (vNext :: xs)) body) =
    resolveExpr uniqueId envDefs contextVars (CExprLambda [v] (CExprLambda (vNext :: xs) body))
resolveExpr uniqueId envDefs contextVars (CExprVariable x) = case resolveVar envDefs contextVars x of
    (Left l) => error l
    (Right r) => success (AExprVariable r, uniqueId)


resolveDecl : Nat -> Vect envLen Identifier -> Vect contextLen Identifier -> CDecl -> Result (ADecl envLen contextLen, Nat)
resolveDecl uniqueId envDefs contextVars (MkCDecl var type) = do
    (t, uniqueId) <- resolveExpr uniqueId envDefs contextVars type
    success (MkADecl t var, uniqueId)

resolveDef : Nat -> Vect envLen Identifier -> Vect contextLen Identifier -> CDef -> Result (ADef envLen contextLen, Nat)
resolveDef uniqueId envDefs contextVars (MkCDef name args body type) =
    if toList contextVars /= reverse args then
        error $ "The context and def params should be the same!"
    else do
        (aBody, uniqueId) <- resolveExpr uniqueId envDefs contextVars body
        (aType, uniqueId) <- resolveExpr uniqueId envDefs contextVars type
        success (MkADef aBody aType name args, uniqueId)

resolveMain : Nat -> Vect envLen Identifier -> Vect contextLen Identifier -> CBook -> Result (ABook envLen contextLen, Nat)
resolveMain uniqueId envDefs contextVars [] = success (ABookNil, uniqueId)
resolveMain uniqueId envDefs contextVars ((CLineDef (MkCDef name args body type)) :: restLines) = do
    extendedEnv <- addToEnv envDefs contextVars name
    (defResolved, uniqueId) <- resolveDef uniqueId envDefs contextVars (MkCDef name args body type)
    (restResolved, uniqueId) <- resolveMain uniqueId extendedEnv contextVars restLines
    success (ABookConsDef defResolved restResolved, uniqueId)
resolveMain uniqueId envDefs contextVars ((CLineSuppose decl body) :: restLines) = do
    (aDecl, uniqueId) <- resolveDecl uniqueId envDefs contextVars decl
    extendedContext <- addToContext envDefs contextVars (var decl)
    (bodyResolved, uniqueId) <- resolveMain uniqueId envDefs extendedContext body
    (restResolved, uniqueId) <- resolveMain uniqueId envDefs contextVars restLines
    success (ABookConsSuppose (MkASuppose aDecl bodyResolved) restResolved, uniqueId)


export
resolve : CBook -> ResolveResultRoot
resolve cBook = do
    (res, uniqueId) <- resolveMain Z [] [] cBook
    success res

export
parseAndResolve_unpacked : SourceString -> ResolveResultRoot
parseAndResolve_unpacked str = do
    p <- parse_unpacked str
    resolve p

export
parseAndResolve : String -> ResolveResultRoot
parseAndResolve str = do
    p <- parse str
    resolve p
