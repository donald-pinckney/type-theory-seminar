module ch1.AST

%default total

public export
data Variable =
      Bound Nat
    | Free String

public export
data Term =
      Var Variable
    | App Term Term
    | Lambda Term
