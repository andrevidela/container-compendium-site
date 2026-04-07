<!-- idris
module Data.Container.Cartesian.Category

import Data.Category
import Data.Category.NaturalTransformation
import Data.Category.Monoid
import Data.Category.Functor

import Data.Container.Definition
import Data.Container.Cartesian
import Data.Container.Category
import Data.Container.Morphism.Definition
import Data.Iso

import Data.Product

import Proofs

%hide Prelude.Ops.infixl.(|>)
--------------------------------------------------------------------------------
-- Cartesian lenses form a category
--------------------------------------------------------------------------------
-->

With the previous definition, we build the required lemmas to prove that it forms a category, first we prove identity.

````lemma
The identity cartesian morphism is neutral when composed on the left.
```idris
0 identityLeft :
    (a, b : Container) -> (f : a =#> b) ->
    Cartesian.identity a |#> f ≡#>≡ f
identityLeft a b (MkCartDepLens fwd bwd) = MkCartDepLensEq
    (\_ => Refl)
    (\f => isoIdRight (bwd f))
```
````
````lemma
The identity cartesian morphism is neutral when composed on the right.
```idris
0 identityRight :
    (a, b : Container) -> (f : a =#> b) ->
    f |#> Cartesian.identity b ≡#>≡ f
identityRight a b (MkCartDepLens f1 bwd) = MkCartDepLensEq (\_ => Refl)
    (\f => isoIdLeft (bwd f))
```
````

Most of the heavy lifting is delegated to `isoIdLeft` \lemref{lem:iso-identities} which it itself part of the proofs that isomophisms form a category.

We do the same for composition which makes use of `transIsoAssoc` \lemref{lem:iso-transitivity}.

````lemma
Composition of cartesian morphisms is associative.
```idris
0 proofComposition :
    (f : a =#> b) -> (g : b =#> c) -> (h : c =#> d) ->
    f |#> (g |#> h) ≡#>≡ (f |#> g) |#> h
proofComposition
  (MkCartDepLens fwd1 bwd1) (MkCartDepLens fwd2 bwd2) (MkCartDepLens fwd3 bwd3) =
  MkCartDepLensEq (\_ => Refl) (\f =>
    symIsoEq $ transIsoAssoc (bwd3 (fwd2 (fwd1 f))) (bwd2 (fwd1 f)) (bwd1 f)
    )
```
````
Finally, using the above, we can write the definition of category in Idris of cartesian container morphisms.
```idris {hidden=""}
||| Cartesian containers category, where objects are containers and morphisms are cartesian lense
public export
```
````proposition
Containers and cartesian morphisms form a category.
```idris
ContCart : Category Container
ContCart = MkCategory
  (\a, b => a =#> b)
  (\_ => identity _)
  Cartesian.(|#>)
  (\_, _, f => cartEqToEq (identityRight _ _ f))
  (\_, _, f => cartEqToEq (identityLeft _ _ f))
  (\_, _, _, _, f, g, h => cartEqToEq (proofComposition f g h))
```
````

We also define a forgetful map into $\Cont$ to easily extract the corresponding lens out of a cartesian morphism.

```idris
public export
toLens : (0 a, b : Container) -> a =#> b -> a =%> b
toLens a b x = x.cfwd <! (\y => to (x.cbwd y))
```

````proposition
There is a forgetful functor $\ContCart → \Cont$
```idris
CartToCont : ContCart ->> Cont
CartToCont = MkFunctor
    { mapObj = Basics.id
    , mapHom = (\x, y => toLens x y)
    , presId = (\_ => Refl)
    , presComp = (\x, y, z, f, g => Refl)
    }
```
````
