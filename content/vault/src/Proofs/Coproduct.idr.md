<!-- idris
module Proofs.Coproduct

import Data.Coproduct
import Data.Iso

public export
-->

````definition
Associativity of coproducts forms an isomorphism.
```idris
assocIso : Iso (a + (b + c)) ((a + b) + c)
assocIso = MkIso assocL assocR assocRLR assocLRL
```
````

