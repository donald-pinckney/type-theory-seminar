module ch2.CST

export
record Identifier where
    constructor MkIdentifier
    text : String

public export
data CType
    = CTypeStar
    | CTypeBox
    | CTypeArrow CType CType
    | CTypeVariable Identifier

export
record CDecl where
    constructor MkCDecl
    var : Identifier
    type : CType

public export
data CExpr
    = CExprPostulate
    | CExprLambda (List CDecl) CExpr
    | CExprVariable Identifier
    | CExprApp CExpr CExpr

export
record CDef where
    constructor MkCDef
    name : Identifier
    args : List Identifier
    body : CExpr
    type : CType

mutual
    public export
    CBook : Type
    CBook = List CLine

    public export
    data CLine
        = CLineDef CDef
        | CLineSuppose CDecl CBook


----- INTERFACE IMPLEMENTATIONS -------------


export
implementation Eq Identifier where
    (MkIdentifier text) == (MkIdentifier x) = text == x

export
implementation Show Identifier where
    show (MkIdentifier text) = text

export
implementation Eq CType where
    CTypeStar == CTypeStar = True
    CTypeBox == CTypeBox = True
    (CTypeArrow x y) == (CTypeArrow z w) = (x == z) && (y == w)
    (CTypeVariable x) == (CTypeVariable y) = x == y
    _ == _ = False

export
implementation Show CType where
    show CTypeStar = "*"
    show CTypeBox = "BOX"
    show (CTypeArrow x y) = "(" ++ (show x) ++ ") -> " ++ show y
    show (CTypeVariable x) = show x

export
implementation Eq CDecl where
    (MkCDecl var type) == (MkCDecl x y) = (var == x) && (type == y)

export
implementation Show CDecl where
    show (MkCDecl var type) = show var ++ " : " ++ show type

export
implementation Eq CExpr where
    CExprPostulate == CExprPostulate = True
    (CExprLambda xs x) == (CExprLambda ys y) = (xs == ys) && x == y
    (CExprVariable x) == (CExprVariable y) = x == y
    (CExprApp x y) == (CExprApp z w) = (x == z) && (y == w)
    _ == _ = False

export
implementation Show CExpr where
    show CExprPostulate = "POSTULATE"
    show (CExprLambda xs x) = "\\" ++ (unwords $ map show xs) ++ " . " ++ (show x)
    show (CExprVariable x) = show x
    show (CExprApp x y) = "(" ++ (show x) ++ " " ++ (show y) ++ ")"


export
implementation Eq CDef where
    (MkCDef name args body type) == (MkCDef x xs y z) = (name == x) && (args == xs) && (body == y) && (type == z)

export
implementation Show CDef where
    show (MkCDef name args body type) = show name ++ "(" ++ (unwords $ map show args) ++ ") := " ++ show body ++ " : " ++ show type

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
