<!-- idris
module Optics.Category

import Optics.Lens
import Data.Category
import Data.Boundary
import Data.Coproduct
import Data.Product
import Proofs
-->

## The category of lenses

Lenses are useful for many aspects of mathematics and programming, the rest of this file
will implement lenses and show that they form a category. This work is not strictly necessary
to use them, but it's important to prove those basic properties if we want to talk about them
in a mathematical context.

Given the previous definitions we only need a couple of lemma to achieve our goal:

- Prove that composing with identity to the left does nothing.
- Prove that composing with identity to the right does nothing.
- Prove that composition is associative.

```idris
||| idLens is the identity when composed to the right
prfidRight : (f : Lens a b) -> (f |> Lens.idLens) ≡ f
prfidRight (MkLens g s) = Refl

||| idLens is the identity when composed to the left
prfIdLeft : (f : Lens a b) -> (Lens.idLens |> f) ≡ f
prfIdLeft (MkLens get set) = Refl

||| composition is associative
prfAssoc : (f : Lens a b) -> (g : Lens b c) -> (h : Lens c d) ->
           (f |> (g |> h)) ≡ ((f |> g) |> h)
prfAssoc {f = (MkLens fget fset)} {g = (MkLens gget gset)} {h = (MkLens hget hset)} = Refl
```

The category of boundary and lenses has boundaries as objects and lenses as morphisms.
Because lens composition is associative, and lenses have an identity `idLens`, we can define the
`Lens` category using our previous definitions:

```idris

||| lenses form a category with composition
export
LensCat : Category Boundary
LensCat = MkCategory
  Lens
  (\_ => idLens)
  (|>)
  (\_, _ => prfidRight)
  (\_, _ => prfIdLeft)
  (\_, _, _, _ => prfAssoc)
```

## (Affine) Traversals

Lenses are not the only data accessor we are going to study, there are a couple more that
we would like to evaluate, the two that will come up later are traversals and affine-traversals.

```idris
public export
record Traversal (a, b : Boundary) where
  constructor MkTraversal
  extract : a.π1 -> Σ Nat (\n => Vect n b.π1 * (Vect n b.π2 -> a.π2))
```

A traversal is a way to iterate on a number of elements, this operation naturally appears when
performing some manipulation using lenses on elements of a list. In the above definition, we use
`n : Nat` to indicate how many elements we are traversing and this in turns informs `Vect  ` Giving us how many elements are expected to be modified. While the above definition makes use of dependent types, it is possible to write it in Haskell using type classes an avoid the reliance on dependent types.

Affine traversals represent a lens that might or might not access the data. When it is accessed, then an update operation is performed, but when it is not. The value is simply returned.
```idris
public export
record Affine (a, b : Boundary) where
  constructor MkAffine
  read : a.π1 -> a.π2 + (b.π1 * (b.π2 -> a.π2))
```

Both those lenses are formulated in a closed way. We're going to see how the closed version and the product of function version are the same in a subsequent module that will also explain the relation between those well known lenses, and monads on containers.
