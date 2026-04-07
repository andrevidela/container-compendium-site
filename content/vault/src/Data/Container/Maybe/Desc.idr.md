
## The Maybe container

In categories of containers by Abbott etc, Containers are used
as _descriptions_ for data structures that carry values. The `Maybe`
type is one of them and can be described as a container using
_the extension on containers_ `Ex : Container -> Type -> Type`.

<!-- idris
module Data.Container.Maybe.Desc

import Data.Container.Coproduct
import Data.Container.Definition
import Data.Container.ForallSeq.Definition
import Data.Container.Morphism
import Data.Container.Morphism.Eq
import Data.Product
import Data.Sigma
import Data.Iso
import Data.Iso.Generic
import Data.Maybe
import Data.Maybe.Any as Maybe.Quantifier
import Proofs

%default total

-- strict version of boolean operations
public export
and : Bool -> Bool -> Bool
and True x = x
and False _ = False

export
andR : {x : Bool} -> and x True === x
andR {x = False} = Refl
andR {x = True} = Refl

export
andAssoc : {x, y, z : Bool} -> (x `and` y) `and` z = x `and` (y `and` z)
andAssoc {x} = ?andAssoc_rhs

public export
or : Bool -> Bool -> Bool
or False x = x
or True _ = True
-->

To define the `Maybe` container, we need to define a boolean predicate. This is nothing more than a dependent type that is indexed over a boolean value, and that is inhabited with a trivial value when the boolean is true.
```idris
public export
data IsTrue : Bool -> Type where
  TT : IsTrue True
```

```idris {hidden=""}
public export
Uninhabited (IsTrue False) where
  uninhabited _ impossible

export
fromTruth : IsTrue x -> x === True
fromTruth TT = Refl

export
allTruths : (x, y : _) -> IsTrue x -> IsTrue y -> x === y
allTruths False _ TT _ impossible
allTruths True False _ TT impossible
allTruths True True z w = Refl

public export
isTrueUniq : (x : IsTrue True) -> TT === x
isTrueUniq TT = Refl
```

Using this predicate, we build the `Maybe` container by setting the shapes as `Bool` and the positions with our `IsTrue` predicate.
````definition {label="def:maybecont"}
The maybe container is given by a boolean and a predicate that this boolean is valued to `True`.
```idris
public export
MaybeCont : Container
MaybeCont = (isJust : Bool) !> IsTrue isJust
```
````

Using this container with the _extension_ \defref{def:extension}, we obtain the `Maybe` functor in $\Set$.

```idris
public export
Maybe : Type -> Type
Maybe = Ex MaybeCont
```

Just like the `Maybe` type of `Prelude`, we can define `Just` and `Nothing` constructors

```idris
public export
Just : (x : a) -> Desc.Maybe a
Just x = MkEx True (\_ => x)

public export
Nothing : Desc.Maybe a
Nothing = MkEx False absurd
```

And we can even prove that they are isomorphic.

````lemma
`Prelude.Maybe` and $⟦MaybeCont⟧$ are isomorphic
```idris
fromDesc : Desc.Maybe a -> Prelude.Maybe a
fromDesc (MkEx False p) = Nothing
fromDesc (MkEx True p) = Just (p TT)

toDesc : Prelude.Maybe a -> Desc.Maybe a
toDesc Nothing = Nothing
toDesc (Just x) = Just x

toFromEq : {0 a : Type} -> (x : Prelude.Maybe a) -> fromDesc (toDesc x) === x
toFromEq Nothing = Refl
toFromEq (Just x) = Refl

0 fromToEq : {0 a : Type} -> (x : Desc.Maybe a) -> toDesc (fromDesc x) === x
fromToEq (MkEx True p) = cong (MkEx True) (funExt $ \TT => Refl)
fromToEq (MkEx False p) = cong (MkEx False) (allUninhabited _ _)

public export
MaybeIso : Desc.Maybe a ≅ Prelude.Maybe a
MaybeIso = MkIso fromDesc toDesc toFromEq fromToEq
```
````

Sometimes it is helpful to define the maybe container as $1 + I$

<!-- idris
public export
-->

```idris
MaybeCont' : Container
MaybeCont' = One + I
```
