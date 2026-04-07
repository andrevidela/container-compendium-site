
<!-- idris
module Data.Container.Morphism

import public Data.Container.Definition
import public Data.Container.Tensor.Definition
import public Data.Container.Sequence.Definition
import public Data.Container.Extension
import public Data.Container.Morphism.Definition
import public Data.Container.Morphism.Context
import public Data.Container.Morphism.Eq
import public Data.Ops
import public Data.Category.Ops
import Data.Coproduct
import Data.Product
import Data.Alg
import Data.Sigma

import Control.Order
import Control.Relation
-->



#### `▷` distributes over `⊗`

This is going to come in handy for composing interactive systems.

```idris

-- ▷ distributes over ⊗
public export
distribProd : (a1 ▷ a2) ⊗ (b1 ▷ b2) =%> (a1 ⊗ b1) ▷ (a2 ⊗ b2)
distribProd =
    (\x => MkEx (x.π1.ex1 && x.π2.ex1) (\vx => x.π1.ex2 vx.π1 && x.π2.ex2 vx.π2 )) <!
    (\x, y => y.π1.π1 ## y.π2.π1 && y.π1.π2 ## y.π2.π2)
```
#### `2 * x = x + x` isomorphism

I'm not going to the implement the entire isomorphism but it works™.
This is useful for the demos of morphisms as servers.

```
-- x + x -> 2 * x
twice : (Bool :- ()) ⊗ x =%> x + x
twice = (\v => if v.π1 then <+ v.π2 else +> v.π2) <!
                   (\case (True && x) => (() &&)
                          (False && x) => (() &&))
```

## Conclusion

I have not written every single monoidal operation on containers, nor all of their properties, but only the ones that I have come across and used for the rest of this work. The realm of containers and their related categories seem to be infinite and there has been decades of mathematical research studying their different aspects. The one thing to take away is that this is just the start and there is already a lot we can do. The natural next step is to look at the [categorical properties of containers](Research/Container-Compendium/src/Data/Container/Category.idr.md)er-Compendium/src/Data/Container/Category.idr.md). If you are more interested in applications, maybe you can skip to how I use containers to write [servers](Research/Container-Compendium/src/Interactive/Server.idr.md)c/Interactive/Server.idr.md).
