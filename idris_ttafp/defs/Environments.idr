module defs.Environments

import Data.Vect
import defs.Identifier

public export
BindingDepth : Type
BindingDepth = (Nat, Nat)

public export
envS : BindingDepth -> BindingDepth
envS (a, b) = (S a, b)

public export
ctxS : BindingDepth -> BindingDepth
ctxS (a, b) = (a, S b)

public export
envDepth : BindingDepth -> Nat
envDepth = fst

public export
ctxDepth : BindingDepth -> Nat
ctxDepth = snd


public export
Env : Nat -> Type
Env n = Vect n Identifier

public export
Context : Nat -> Type
Context n = Vect n Identifier
