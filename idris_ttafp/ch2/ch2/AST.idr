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

public export
data Type' =
      VarType TypeVariable
    | Arrow Type' Type'

public export
data Term =
      Var TermVariable
    | App Term Term
    | Lambda Type' Term
