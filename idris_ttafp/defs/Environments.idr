module defs.Environments

import Data.Vect
import defs.Identifier

public export
Env : Nat -> Type
Env n = Vect n Identifier

public export
Context : Nat -> Type
Context n = Vect n Identifier

