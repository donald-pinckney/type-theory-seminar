module ch1.AST

public export
data Variable =
      Bound Nat
    | Free String

public export
data Term =
      Var Variable
    | App Term Term
    | Lambda Term
