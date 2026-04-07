<!-- idris
module Data.Container.Tensor.Definition

import Data.Container.Definition
import public Data.Product
-->

### Tensor product

The tensor product of container combines with the cartesian product both the queries and the responses. This is not to be confused with the
cartesian product on containers \defref{def:product-cont}

<!-- idris
public export
-->

````definition {label="def:tensor-cont"}
The tensor product of container.
```idris
(⊗) : (c1, c2 : Container) -> Container
(⊗) c1 c2 = (x : c1.req * c2.req) !> c1.res x.π1 * c2.res x.π2
```
````
