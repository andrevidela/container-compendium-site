
To prove it is a monoidal product, we need some more basic facts, for example
that it is a bifunctor. As customary, we introduce a map on morphisms for
the tensor product. This map will be used as a combinator for running two dependent lenses
in parallel.

<!-- idris
module Data.Container.Tensor.Bifunctor

import Data.Category
import Data.Category.Functor
import Data.Category.Bifunctor

import Data.Container.Category
import Data.Container.Definition
import Data.Container.Morphism.Definition
import Data.Container.Tensor.Definition

public export
-->
```idris
(~⊗~) : (a =%> b) -> (a' =%> b') -> a ⊗ a' =%> b ⊗ b'
(~⊗~) x y = (bimap x.fwd y.fwd) <! (\v, w => x.bwd v.π1 w.π1 && y.bwd v.π2 w.π2)
```

<!-- idris
public export
-->
We also give is a name that's easier to pronounce than `~⊗~`.
```idris
parallel : (a =%> b) -> (a' =%> b') -> a ⊗ a' =%> b ⊗ b'
parallel = (~⊗~)
```

<!-- idris
public export
-->
From this we can build the proof that it forms a bifunctor in $\Cont$
```idris
TensorBifunctor : Bifunctor Cont Cont Cont
TensorBifunctor = MkFunctor
    (uncurry (⊗))
    (\x, y, m => m.π1 ~⊗~ m.π2)
    (\v => depLensEqToEq $ MkDepLensEq
        (\vx => prodUniq vx)
        (\vx, vy => prodUniq vy)
    )
    (\a, b, c, f, g => Refl)
```
