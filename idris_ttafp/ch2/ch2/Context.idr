module ch2.Context

import ch2.AST

public export
FreeDeclaration : Type
FreeDeclaration = (FreeTermVariable, Type')

public export
BoundDeclaration : Type
BoundDeclaration = Type'


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
    uniqueFreeDecls : (decls : List FreeDeclaration ** UniqueFreeDeclarations decls)
    boundDecls : List BoundDeclaration -- This is a stack, head being the top

public export
freeDecls : Context -> List FreeDeclaration
freeDecls (MkContext (x ** pf) boundDecls) = x

export
push : BoundDeclaration -> Context -> Context
push d (MkContext freeDecls boundDecls) = MkContext freeDecls (d :: boundDecls)

public export
data ValueAtKey : Type' -> (xs : List FreeDeclaration) -> FreeTermVariable -> Type where
    ThisKey : ValueAtKey x ((k, x) :: xs) k
    OtherKey : UniqueFreeDeclarations (p :: xs) -> ValueAtKey x xs k -> ValueAtKey x (p :: xs) k

export
unOtherKey : ValueAtKey x ((w, y) :: ps) v -> Not (v = w) -> ValueAtKey x ps v
unOtherKey ThisKey v_neq_w = void $ v_neq_w Refl
unOtherKey (OtherKey unique other) v_neq_w = other

implementation Uninhabited (FreeDeclarationListElem v []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

implementation Uninhabited (UniqueFreeDeclarations ((v, a) :: (v, b) :: rest)) where
  uninhabited (ConsValid not_elem x) = not_elem Here

export
implementation Uninhabited (ValueAtKey x [] k) where
  uninhabited ThisKey impossible
  uninhabited (OtherKey _ _) impossible

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

export
uniqueUnCons : UniqueFreeDeclarations (x :: xs) -> UniqueFreeDeclarations xs
uniqueUnCons (ConsValid f x) = x


isUniqueFreeDeclarations : (decls : List FreeDeclaration) -> Dec (UniqueFreeDeclarations decls)
isUniqueFreeDeclarations [] = Yes NilValid
isUniqueFreeDeclarations ((v, t) :: xs) =
    case isUniqueFreeDeclarations xs of
        (No same_tail) => No (nonUniqueCons same_tail)
        (Yes unique_tail) => case isContextListElem v xs of
            (No unique_head) => Yes (ConsValid unique_head unique_tail)
            (Yes same_head) => No (repeatNonUnique same_head)
