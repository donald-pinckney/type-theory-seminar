module ch2.AST

public export
data TermVariable =
      Bound Nat
    | Free String

public export
data TypeVariable =
    FreeType String

public export
data Type' =
      VarType TypeVariable
    | Arrow Type Type

public export
data Term =
      Var TermVariable
    | App Term Term
    | Lambda Type' Term
