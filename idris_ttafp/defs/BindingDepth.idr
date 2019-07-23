module defs.BindingDepth

import Data.Vect
import defs.Identifier

%default total

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
EnvNames : Nat -> Type
EnvNames n = Vect n Identifier

public export
ContextNames : Nat -> Type
ContextNames n = Vect n Identifier
