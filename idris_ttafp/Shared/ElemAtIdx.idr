module ElemAtIdx

||| A proof that some element is found in a list at some specified index.
|||
||| Example: `the (ElemAtIdx "bar" 1 ["foo", "bar", "baz"])`
public export
data ElemAtIdx : a -> (xs : List a) -> Nat -> Type where
     ||| A proof that the element is at the front of the list.
     |||
     ||| Example: `the (ElemAtIdx "a" 0 ["a", "b"]) Here`
     HereZ : ElemAtIdx x (x :: xs) Z
     ||| A proof that the element is after the front of the list
     |||
     ||| Example: `the (ElemAtIdx "b" 1 ["a", "b"]) (There Here)`
     ThereS : (later : ElemAtIdx x xs n) -> ElemAtIdx x (y :: xs) (S n)


export
implementation Uninhabited (ElemAtIdx x [] n) where
  uninhabited HereZ impossible
  uninhabited (ThereS _) impossible

export
unThereS : ElemAtIdx x (y :: ys) (S n) -> ElemAtIdx x ys n
unThereS (ThereS later) = later
