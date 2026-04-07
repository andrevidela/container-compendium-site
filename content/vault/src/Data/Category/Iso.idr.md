<!-- idris
module Data.Category.Iso

import Data.Category
import Data.Iso
-->

### The Category of Isomorphisms

Isomorphisms form a category where the objects are types, just like $\Set$ \defref{def:set-cat} but the morphisms are not function but isomorphisms \defref{def:iso}. The identity is given by the identity isomorphism, and the composition by transitivity of isomorphisms. In a sense, the category $\Set$ is a sub-category of $\cat{Iso}$ where only the "to" map is kept and everything else is thrown away.

```idris {hidden=""}
public export
```

````proposition {label="iso-cat"}
Isomorphisms form a category $\cat{Iso}$.
```idris
IsoCat : Category Type
IsoCat = NewCat
  { objects = Type
  , morphisms = (≅)
  , identity = (\x => Iso.identity _)
  , composition = transIso
  , identity_right = (\x => fromIsoEq _ _ (isoIdRight x))
  , identity_left = (\x => fromIsoEq _ _ (isoIdLeft x))
  , compose_assoc = (\x, y, z => fromIsoEq _ _ (transIsoAssoc x y z))
  }
```
````
