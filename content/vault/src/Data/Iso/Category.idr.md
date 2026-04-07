<!-- idris
module Data.Iso.Category

import public Data.Iso.Generic
import Data.Category

import public Control.Relation
-->

A category gives rise to a reflexive relation via its identity morphism.
```idris
%hint public export
RCat : {cat : _} -> Reflexive cat.obj ((~:>) cat)
RCat = MkReflexive (cat.id _)
```

A category gives rise to a transitive relation via its composition of morphisms.
```idris
%hint public export
TCat : {cat : _} -> Transitive cat.obj ((~:>) cat)
TCat = MkTransitive $
    \ f, g => (|:>) cat f g
```

Isomorphisms between two objects of a category.

```idris
public export
CatIso : {0 o : Type} -> (cat : Category o) -> (a, b : o) -> Type
CatIso cat a b = GenIso o ((~:>) cat) (===) {tx = TCat, rx = RCat} a b
```
