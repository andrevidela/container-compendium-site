
There has been many definition given for lenses and their siblings. Here we breifly summarise what they are and how they relate to each others

## All the definitions of lenses

The following is all equivalent

### Function

```
Lens : (s, t, a, b : Type) -> Type
Lens s t a b = a -> s * (t -> b)
```

### VanLaarhoven

```
VLHLens : (s, t, a, b : Type) -> Type
VLHLens s t a b = ∀ f : functor. (s -> f t) -> a -> f b
```

### Dependent

```
DLens : (s, t, a, b : Type) -> Type
DLens s t a b = (a, b) => (s, t)
```

````lemma
All the definitions of lenses are isomorphic
````

This is true because the dependent version and the function version are isomorphic by definition. The funcion version is isomorphi to the vanlaarhoven verion by

## All the definitions of Traversals

The following is all equivalent

### Function


```
Traversal : (s, t, a, b : Type) -> Type
Traversal s t a b = a -> \Sigma (n : Nat) | Vect n s * (Vect n t -> b))
```

### VanLaarhoven

```
VLHTraversal : (s, t, a, b : Type) -> Type
VLHTraversal s t a b = ∀ f : Applicative. (s -> f t) -> a -> f b
```

### Dependent

```
Affine : (s, t, a, b : Type) -> Type
Affine s t a b = (a, b) => All.List (s, t)
```

### Notes

It's interesting to as what type corresponds to

```
Affine? : (s, t, a, b : Type) -> Type
Affine? s t a b = (a, b) => Any.List (s, t)
```

where we use `Any` lists instead of `All`. To find out, we derive the following equivalences:

```
Any.List (s, t)
~
(List s, Any t)
~
Σ (xs : List s) . Σ (x ∈ xs) . t x
~ remove dependency for t
List s * t
```

Plugging in this definition as a non-dependent function we get:

```
Traversal? : (s, t, a, b : Type) -> Type
Traversal? s t a b = a -> List s * (t -> b)
```

## All the definitions of Affine traversals

The following is all equivalent

### Function

```
Affine : (s, t, a, b : Type) -> Type
Affine s t a b = a -> b + (s * (t -> b))
```

### VanLaarhoven

```
VLHAffine : (s, t, a, b : Type) -> Type
VLHAffine s t a b = ∀ f : Pointed. (s -> f t) -> a -> f b
```

### Dependent

```
Affine : (s, t, a, b : Type) -> Type
Affine s t a b = (a, b) => Any.Maybe (s, t)
```

### Note

Like traversal, we can flip the `Any` for its counterpart and find out what the non-dependent version of the type matches.

```
Any.Maybe (s, t)
~ by def
(Maybe s, Any t)
~
Σ (x : s) . t x
~ remove dependencies
s * t
```

Leading to the definition as a non-dependent lens

```
Affine? : (s, t, a, b : Type) -> Type
Affine? s t a b = a -> s * (t -> b)
```

Which is just a lens.

This conclusion is a bit curious but it highlights a big difference in the semantics expressible by the types of each representations. A dependent lens `a => Any.Maybe b` says "If we fail in the forward part, then it's over, there is nothing we can do" it does not necessarily mean that the forward part _must_ success, only that _if it fails_, this lens is unable to deal with the error. In the land of non-dependent lenses this behaviour would be represented by a normal lens `Lens s t a b` but that can throw an exception, and another lens must catch the exception and deal with the error. This error-handling control flow is not representable in normal lenses, but in the category of containers it gets its own type.

## All the definitions of Kleene Star

The following is all equivalent

### Function Style

This is the free monad on the store comonad

```
Kleene : (s, t, a, b : Type) -> Type
Kleene s t a b = a -> Fix (\x . b * (s -> x) + t)
```

### VanLaarhoven

```
VLHKleene : (s, t, a, b : Type) -> Type
VLHKleene s t a b = ∀ f : Monad. (s -> f t) -> a -> f b
```

### Dependent

```
DKleene : (s, t, a, b : Type) -> Type
DKleene s t a b = (a, b) => Star (s, t)
```

### Notes: Monad?

I don't actually know if the kleene star is a monad in Cont, I suspect not, but maybe I haven't tried hard enough. In either case it's good news:

- if it's not a monad, it would  explain why the VLH lens people have such distaste for `Monad`. they say it's because monads don't compose, but it's deeper than that, it's because the kleene star isn't a monad.
- If it's a monad, it explains why VLH cannot compose them nicely, because they are stuck at the level of types but they need monads on containers to properly chain them.

### Notes: Distributive laws?

One of the annoying things with the kleene star is that it doesn't distribute across coproducts. That makes sense, the composition product ensure an appropriate sequence of operations, but it makes error handling a pain in the ass.

It distributes over tensor though which is good and we should be able to use that as a synchronisation point in a chain of compositions.
