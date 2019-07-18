module defs.CST

import defs.Identifier

mutual
    public export
    record CDecl where
        constructor MkCDecl
        var : Identifier
        type : CExpr

    public export
    data CExpr
        = CExprStar
        | CExprBox
        | CExprArrow (Either CExpr CDecl) CExpr
        | CExprPostulate
        | CExprLambda (List CDecl) CExpr
        | CExprApp CExpr CExpr
        | CExprVariable Identifier
        | CExprDefArgs (List CExpr)

export
record CDef where
    constructor MkCDef
    name : Identifier
    args : List Identifier
    body : CExpr
    type : CExpr

mutual
    public export
    CBook : Type
    CBook = List CLine

    public export
    data CLine
        = CLineDef CDef
        | CLineSuppose CDecl CBook


--------- INTERFACE IMPLEMENTATIONS -------------

mutual
    export
    implementation Eq CDecl where
        (MkCDecl var type) == (MkCDecl x y) = (var == x) && (type == y)

    export
    implementation Show CDecl where
        show (MkCDecl var type) = show var ++ " : " ++ show type

    total
    eq_decl_list : List CDecl -> List CDecl -> Bool
    eq_decl_list [] [] = True
    eq_decl_list [] (x :: xs) = False
    eq_decl_list (x :: xs) [] = False
    eq_decl_list (x :: xs) (y :: ys) = (x == y) && (eq_decl_list xs ys)


    total
    expr_lists_eq : List CExpr -> List CExpr -> Bool
    expr_lists_eq [] [] = True
    expr_lists_eq [] (x :: xs) = False
    expr_lists_eq (x :: xs) [] = False
    expr_lists_eq (x :: xs) (y :: ys) = (x == y) && (expr_lists_eq xs ys)

    implementation Eq CExpr where
        CExprPostulate == CExprPostulate = True
        (CExprLambda xs x) == (CExprLambda ys y) = (eq_decl_list xs ys) && (x == y)
        (CExprVariable x) == (CExprVariable y) = x == y
        (CExprApp x y) == (CExprApp z w) = (x == z) && (y == w)
        CExprStar == CExprStar = True
        CExprBox == CExprBox = True
        (CExprDefArgs xs) == (CExprDefArgs ys) = expr_lists_eq xs ys
        (CExprArrow (Left l) y) == (CExprArrow (Left x) w) = (l == x) && (y == w)
        (CExprArrow (Left l) y) == (CExprArrow (Right r) w) = False
        (CExprArrow (Right r) y) == (CExprArrow (Left l) w) = False
        (CExprArrow (Right r) y) == (CExprArrow (Right x) w) = (r == x) && (y == w)
        _ == _ = False



    export
    implementation Show CExpr where
        show CExprPostulate = "POSTULATE"
        show (CExprLambda xs x) = "\\" ++ (unwords $ map show xs) ++ " . " ++ (show x)
        show (CExprVariable x) = show x
        show (CExprApp x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"
        show CExprStar = "*"
        show CExprBox = "BOX"
        show (CExprDefArgs args) = "{" ++ show args ++ "}"
        show (CExprArrow (Left t) y) = "(" ++ (show t) ++ ") -> " ++ show y
        show (CExprArrow (Right td) y) = "(" ++ (show td) ++ ") -> " ++ show y


export
implementation Eq CDef where
    (MkCDef name args body type) == (MkCDef x xs y z) = (name == x) && (args == xs) && (body == y) && (type == z)

export
implementation Show CDef where
    show (MkCDef name args body type) = show name ++ "(" ++ (unwords $ map show args) ++ ") := " ++ show body ++ " : " ++ show type


-- Have to do a bunch of gymnastics to convince Idris of totality
total suppose_eq : (aDef : CDecl) -> (aBook : CBook) -> (bDef : CDecl) -> (bBook : CBook) -> Bool
suppose_eq aDef [] bDef [] = aDef == bDef
suppose_eq aDef [] bDef (x :: xs) = False
suppose_eq aDef (x :: xs) bDef [] = False
suppose_eq aDef ((CLineDef x) :: xs) bDef ((CLineDef y) :: ys) = x == y && suppose_eq aDef xs bDef ys
suppose_eq aDef ((CLineDef x) :: xs) bDef ((CLineSuppose y zs) :: ys) = False
suppose_eq aDef ((CLineSuppose x zs) :: xs) bDef ((CLineDef y) :: ys) = False
suppose_eq aDef ((CLineSuppose x zs) :: xs) bDef ((CLineSuppose y ws) :: ys) = suppose_eq x zs y ws && suppose_eq aDef xs bDef ys

export
implementation Eq CLine where
    (CLineDef x) == (CLineDef y) = x == y
    (CLineDef x) == (CLineSuppose y xs) = False
    (CLineSuppose x xs) == (CLineDef y) = False
    (CLineSuppose x xs) == (CLineSuppose y ys) = suppose_eq x xs y ys

export
implementation Show CLine where
    show (CLineDef x) = show x
    show (CLineSuppose x xs) = "(Suppose " ++ show x ++ "; " ++ show xs ++ ")"
