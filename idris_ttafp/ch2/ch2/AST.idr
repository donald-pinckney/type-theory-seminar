module ch2.AST


public export
FreeTermVariable : Type
FreeTermVariable = String

-- export
-- BoundTermVariable

-- implementation

public export
data TermVariable =
      Bound Nat
    | Free FreeTermVariable

public export
data TypeVariable =
    FreeType String

implementation DecEq TypeVariable where
  decEq (FreeType x) (FreeType y) = case decEq x y of
      (Yes Refl) => Yes Refl
      (No contra) => No (\prf => case prf of Refl => contra Refl)

public export
data Type' =
      VarType TypeVariable
    | Arrow Type' Type'

export
implementation DecEq Type' where
  decEq (VarType x) (VarType y) = case decEq x y of
      (Yes Refl) => Yes Refl
      (No contra) => No (\Refl => contra Refl)
  decEq (VarType x) (Arrow y z) = No (\prf => case prf of Refl impossible)
  decEq (Arrow x y) (VarType z) = No (\prf => case prf of Refl impossible)
  decEq (Arrow x y) (Arrow z w) = case (decEq x z, decEq y w) of
      (Yes Refl, Yes Refl) => Yes Refl
      (Yes Refl, No y_neq_w) => No (\Refl => y_neq_w Refl)
      (No x_neq_z, Yes Refl) => No (\prf => case prf of Refl => x_neq_z Refl)
      (No x_neq_z, No y_neq_w) => No (\prf => case prf of Refl => x_neq_z Refl)


public export
data Term =
      Var TermVariable
    | App Term Term
    | Lambda Type' Term
