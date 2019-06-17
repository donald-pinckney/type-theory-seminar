module ch2.Context

import ch2.AST

public export
FreeDeclaration : Type
FreeDeclaration = (FreeTermVariable, Type')

public export
BoundDeclaration : Type
BoundDeclaration = Type'

public export
record Statement where
    constructor MkStatement
    term : Term
    type : Type'


-- Forward declaration because of bug in totality checker with mutual blocks.
-- See https://github.com/idris-lang/Idris-dev/issues/4436
public export
data FreeDeclarationListElem : FreeTermVariable -> List FreeDeclaration -> Type

public export
data UniqueFreeDeclarations : List FreeDeclaration -> Type where
    NilValid : UniqueFreeDeclarations []
    ConsValid : Not (FreeDeclarationListElem v xs) -> UniqueFreeDeclarations xs -> UniqueFreeDeclarations ((v, t) :: xs)

public export
data FreeDeclarationListElem : FreeTermVariable -> List FreeDeclaration -> Type where
    Here : FreeDeclarationListElem v ((v, t) :: xs)
    There : (later : FreeDeclarationListElem v xs) -> FreeDeclarationListElem v (w :: xs)


public export
record Context where
    constructor MkContext
    freeDeclarations : (freeDecls : List FreeDeclaration ** UniqueFreeDeclarations freeDecls)
    boundDecls : List BoundDeclaration -- This is a stack, head being the top

public export
record Judgment where
    constructor MkJudgment
    context : Context
    statement : Statement


implementation Uninhabited (FreeDeclarationListElem v []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

implementation Uninhabited (UniqueFreeDeclarations ((v, a) :: (v, b) :: rest)) where
  uninhabited (ConsValid not_elem x) = not_elem Here

isContextListElem : (v : FreeTermVariable) -> (decls : List FreeDeclaration) -> Dec (FreeDeclarationListElem v decls)
isContextListElem v [] = No uninhabited
isContextListElem v ((w, t) :: xs) = case decEq v w of
    (Yes Refl) => Yes Here
    (No not_head) => case isContextListElem v xs of
        (Yes prf) => Yes (There prf)
        (No not_tail) => No (\isElem => case isElem of
                Here => not_head Refl
                (There later) => not_tail later
            )


repeatNonUnique : FreeDeclarationListElem v xs -> Not (UniqueFreeDeclarations ((v, t) :: xs))
repeatNonUnique {xs = ((v, t) :: ys)} Here unique = absurd unique
repeatNonUnique {xs = (w :: ys)} (There later) (ConsValid not_elem unique) = not_elem (There later)

nonUniqueCons : Not (UniqueFreeDeclarations xs) -> Not (UniqueFreeDeclarations (d :: xs))
nonUniqueCons same_tail unique = case unique of
    (ConsValid f unique_tail) => same_tail unique_tail

isUniqueFreeDeclarations : (decls : List FreeDeclaration) -> Dec (UniqueFreeDeclarations decls)
isUniqueFreeDeclarations [] = Yes NilValid
isUniqueFreeDeclarations ((v, t) :: xs) =
    case isUniqueFreeDeclarations xs of
        (No same_tail) => No (nonUniqueCons same_tail)
        (Yes unique_tail) => case isContextListElem v xs of
            (No unique_head) => Yes (ConsValid unique_head unique_tail)
            (Yes same_head) => No (repeatNonUnique same_head)
