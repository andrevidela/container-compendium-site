<!-- idris
module Data.Container.Cartesian.Tensor.Bifunctor

import Data.Container.Definition
import Data.Container.Category
import Data.Container.Tensor.Definition
import Data.Container.Morphism.Definition
import Data.Container.Cartesian
import Data.Container.Cartesian.Category

import Data.Product
import Data.Iso

import Data.Category.Bifunctor
import Data.Category.Monoid
import Data.Category.NaturalTransformation
import Data.Category.Bicategory
import Data.Category.Bicategory.Para

import Proofs

%hide Prelude.Ops.infixl.(*>)
-->

### Tensor is a Bifunctor in $\ContCart$

This definition is necessary to define the fact that $\ContCart$ is monoidal.

We extract the map on morphisms as it is quite handy to use directly.
<!-- idris
export infixl 8 ~⊗#~
public export
-->

```idris
(~⊗#~) : (a =#> b) -> (a' =#> b') -> a ⊗ a' =#> b ⊗ b'
(~⊗#~) x y = MkCartDepLens (bimap x.cfwd y.cfwd)
    (\v => IsoProd (x.cbwd v.π1) (y.cbwd v.π2))
```
<!-- idris
public export
-->

Using it we define the bifunctor $\ContCart×\ContCart→\ContCart$.

````proposition
Tensor forms a bifunctor $\ContCart × \ContCart → \ContCart$
```idris
TensorBifunctorCart : Bifunctor ContCart ContCart ContCart
TensorBifunctorCart = MkFunctor
    (uncurry (⊗))
    (\x, y, m => m.π1 ~⊗#~ m.π2)
    -- proofs in appendix
```
```idris {hidden=""}
    (\v => cartEqToEq
         $ MkCartDepLensEq
           (\(x && y) => Refl)
           (\(x && y) => MkIsoEq (\(x && y) => Refl)
                                 (\(x && y) => Refl)
           )
    )
    (\a, b, c, f, g =>
        cartEqToEq
        $ MkCartDepLensEq
            (\x => Refl)
            (\(x && y) => MkIsoEq (\w => ?iii) (\w => ?ahhu)))
```
````
