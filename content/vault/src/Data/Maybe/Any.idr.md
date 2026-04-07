### Maybe Any

Like lists, `Maybe` has two predicate transformers, `Any` and `All`. `Any` is only in habited whenever its index is `Just`.

<!-- idris
module Data.Maybe.Any
import Data.Maybe.Monad

||| Types of indexed maybe values that are always present
public export
-->

````definition {label="def:maybe-any"}
The Any predicate transformer is only in habited when the `Maybe` index is `Just`.
```idris
data Any : (x -> Type) -> Maybe x -> Type where
  Aye : {v : x} -> pred v -> Any pred (Just v)
```
````

````proposition
We can always extract the predicate from `Any`.
```idris {hidden=""}
public export
```
```idris
(.unwrap) : Any p (Just x) -> p x
(.unwrap) (Aye y) = y
```
````

```idris {hidden=""}
public export
```
````proposition
`Any` is uninhabited when the index is `Nothing`.
```idris
Uninhabited (Any p Nothing) where
  uninhabited _ impossible
```
````

```idris
public export
anyFunctorMap :
    {0 a, b : Type} -> {0 a' : a -> Type} -> {0 b' : b -> Type} ->
    (fw : a -> b) -> (bw : (x : a) -> b' (fw x) -> a' x) ->
    (y : Maybe a) ->
    (z : Any b' (map fw y)) ->
    Any a' y
anyFunctorMap fw bw (Just x) y = Aye (bw x y.unwrap)

public export
anyJoin : {0 a : Type} -> {0 p : a -> Type} ->
          (x : Maybe (Maybe a)) ->
          Any p (joinMaybe x) ->
          Any (\x => Any p x) x
anyJoin Nothing y = absurd y
anyJoin (Just x) y = Aye y
```
