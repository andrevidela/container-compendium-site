<!-- idris
module Data.Maybe.Monad

import Data.Category
import Data.Category.Functor
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.NaturalTransformation

public export
-->

#### The Maybe Monad

It is well documented that the `Maybe` type as defined by `data Maybe a = Nothing | Just a`
is a monad in $\Set$. The following demonstrates that in our categorical framework by first
ensuring it's a well-behaved functor, and then proving that its `join` and `pure` method
respect the usual monad conditions.

```idris {hidden=""}
maybeFunctorCompose :
    {0 a, b, c : Type} ->
    (f : b -> c) -> (g : a -> b) -> (x : Maybe a) ->
    map f (map g x) === map (f . g) x
maybeFunctorCompose f g Nothing = Refl
maybeFunctorCompose f g (Just x) = Refl

public export
maybeFunctorId : (xs : Maybe a) -> map Prelude.id xs === xs
maybeFunctorId Nothing = Refl
maybeFunctorId (Just x) = Refl
```



<!-- idris
public export
-->
```idris {caption="The maybe functor is using the Maybe type to map objects and the map function to map morphisms" label="fig:maybe-functor"}
MaybeIsFunctor : Endo Set
MaybeIsFunctor = MkFunctor
  Maybe
  (\_, _ => map)
  (\_ => funExt maybeFunctorId)
  (\a, b, c, f, g => sym $ funExt $ maybeFunctorCompose g f)
```

To prove it is a monad we give definitions for `join`. `pure` is given by the `Just` constructor.

<!-- idris
public export
-->

```idris {caption="Join on Maybe" label="fig:join-maybe"}
joinMaybe : Maybe (Maybe a) -> Maybe a
joinMaybe Nothing = Nothing
joinMaybe (Just a) = a
```
<!-- idris
%unbound_implicits off
export
-->
```idris {caption="Proof that join and map commute" label="fig:join-map-commute"}
joinMaybeMap :
    {0 a : Type} ->
    (x : Maybe (Maybe (Maybe a))) ->
    joinMaybe (map joinMaybe x) ≡ joinMaybe (joinMaybe {a = Maybe a}  x)
joinMaybeMap Nothing = Refl
joinMaybeMap (Just x) = Refl
```
<!-- idris
export
-->
```idris {caption="Proof that join and pure commute" label="fig:join-unit-commute"}
joinMapId : {0 a : Type} ->
            (x : Maybe a) -> joinMaybe (map Just x) ≡ x
joinMapId Nothing = Refl
joinMapId (Just x) = Refl
```

<!-- idris
%unbound_implicits on
public export
-->
```idris
MaybeIsMonad : Monad Set MaybeIsFunctor
MaybeIsMonad = MkMonad
  (MkNT
    (\_ => Just)
    (\_, _, m => Refl))
  (MkNT
    (\_ => joinMaybe)
    (\a, b, m => funExt $ \case Nothing => Refl
                                (Just x) => Refl)
    )
  (\_ => funExt joinMaybeMap)
  (\_ => Refl)
  (\_ => funExt joinMapId)
```
