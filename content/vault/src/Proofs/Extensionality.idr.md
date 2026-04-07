<!-- idris
module Proofs.Extensionality

export
-->

### Function Extensionality

Idris does not feature function extensionality like OTT or HoTT, and because of our use of propositional equality,
we have to postulate it to use it.

````postulate
Function extensionality.
```idris
0 funExt : {f, g : a -> b} -> ((x : a) -> f x === g x) ->  f === g
```
````
```idris {hidden=""}
export
```
Sometimes we need a dependent version of function extensionalty as well.
````postulate
Dependent function extensionality.
```idris
0 funExtDep : {a : Type} -> {b : a -> Type} -> {f, g : (x : a) -> b x} ->
              ((x : a) -> f x === g x) ->  f === g
```
````

```idris {hidden=""}
export 0
hfunExt : {f : a -> b} -> {g : c -> b} -> (prf : a === c) -> ((x : a) -> f x === g (replace {p=Basics.id} prf x)) ->  f === replace {p = \x => x -> b} (sym prf) g
hfunExt Refl = funExt

export 0
funExtDep0 : {a : Type} -> {b : a -> Type} -> {f, g : (0 x : a) -> b x} -> ((0 x : a) -> f x = g x) ->  f = g

export
0 funExt2Dep : {a : Type} -> {b : a -> Type} -> {c : a -> Type} -> {f, g : (x : a) -> b x -> c x} -> ((x : a) -> (y : b x) -> f x y = g x y) ->  f = g


export 0
funExt2 : {f, g : a -> b -> c} -> ((x : a) -> (y : b) -> f x y = g x y) ->  f = g


export
```


````lemma
Given an equality between two functions $f : a → b$ and $g : a → b$  we can obtain
the equality $f x ≡ f x$ given a value $x : a$.
```idris
applySame : {f, g : a -> b} -> (x : a) -> f === g -> f x === g x
applySame x Refl = Refl
```
````
