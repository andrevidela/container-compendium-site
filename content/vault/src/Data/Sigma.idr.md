<!-- idris
module Data.Sigma

import Data.Ops

import Proofs.Equality

public export
-->
### Sigma Types

One of the cornerstones of dependently types programing is `Σ`-types. They can have many interpretations:

- A dependent pair where the second value's type depends on the first
- An existential quantifier for a predicate
- The dependent coproduct over indexed types

````definition
A dependent pair is given by a type $a$ and another type $b : a → Type$ indexed over $a$.
```idris
typebind
record Σ (a : Type) (b : a -> Type) where
  constructor (##)
  ||| First projection of sigma
  π1 : a
  ||| Second projection of sigma
  π2 : b π1
```
````

Notice the use of the `typebind` keyword on the record declaration. This allows us to write
`Σ (n : Nat) | Fin n` without having to use a lambda to bind `n`.

Like before, here is a selection of helper function and properties about `Σ`-types.

```idris {hidden=""}
%name (##) p1, p2
%pair Σ π1 π2
```

The first fact of note is that Σ-types can define both products and coproducts

````proposition
Products are given by a Σ-type where the second projection does not depend
on the first.
```idris
Product : Type -> Type -> Type
Product a b = Σ (_ : a) | b
```
````
````proposition
Coproducts are given by a Σ-type where the first projection is a choice of type, and the second projection is the type selected.
```idris
Coproduct : Type -> Type -> Type
Coproduct a b = Σ (isLeft : Bool) | if isLeft then a else b
```
````

- [ ] add currying

```idris {hidden=""}
public export
elimSig : {0 a : Type} -> {0 b : a -> Type} ->
          {0 d : Σ a b -> Type} ->
          (s : Σ a b) -> ((x : a) -> (y : b x) -> (p : x === s.π1) -> (y ≡≡ s.π2) {p = b} -> d (x ## y)) -> d s
elimSig (p1 ## p2) f = f p1 p2 Refl (IRefl Refl)

export
Uninhabited a => Uninhabited (Σ a b) where
  uninhabited x = absurd x.π1
```
