<!-- idris
module Data.Container.Coproduct.Definition

import Data.Container.Definition

import public Data.Coproduct

public export
-->

### Coproduct

When given two container that represent query and responses,
we can build a new container that represents the choice of either
picking the first interaction mode, or the second. This way of
combining two containers is the essence of the coproduct.

````definition
The coproduct of $\cbar{A}$ and $\cbar{B}$ is given by $(A + B, [\bar{A}, \bar{B}])$.
```idris
(+) : (c1, c2 : Container) -> Container
(+) c1 c2 =
  (q : c1.request + c2.request) !> choice c1.response c2.response q
```
````
