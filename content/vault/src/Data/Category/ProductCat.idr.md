<!-- idris
module Data.Category.ProductCat

import Data.Category
import Data.Category.Functor
import Data.Category.Product
-->


## Product of Categories

Given two categories $\cat{C}, \cat{D}$, the _product category_ combines both by having
using the catesian product of objects in $\cat{C}$ and $\cat{D}$ for its set of objects,
and the cartesian product of morphisms in $\cat{C}$ and $\cat{D}$ for its set of morphisms.

````definition
The product category $\cat{C} × \cat{D}$ has
- objects $|\cat{C}| * |\cat{D}|$
- morphisms $∀ x, y ∈ \cat{C}, z, w ∈ \cat{D}. \mor{C}{x}{y} × \mor{D}{z}{w}$
- identity given by the pair of identity morphisms $id_{\cat{C} × \cat{D}} = id_{\cat{C}} * id_{\cat{D}}$
- composition given by the pair of the composition of morphisms in $\cat{C}$ and $\cat{D}$ $;_{\cat{C} × \cat{D}} = ;_{\cat{C}} * ;_{\cat{D}}$
````

In this definition $*$ is the cartesian product in $\Set$ and $×$ is the product of categories. We reproduce this convention in Idris.

```idris {hidden=""}
public export
```

```idris
(×) : Category o -> Category p -> Category (o * p)
(×) x y = MkCategory
  (\a, b => ((~:>) x a.π1 b.π1) * ((~:>) y a.π2 b.π2))
  (\v => x.id v.π1 && y.id v.π2)
  (\f, g => (|:>) x f.π1 g.π1 && (|:>) y f.π2 g.π2)
  (\_, _, idl => cong2 (&&)
      (x.idRight _ _ idl.π1)
      (y.idRight _ _ idl.π2) `trans` Data.Product.projIdentity idl
  )
  (\_, _, idr => cong2 (&&)
      (x.idLeft  _ _ idr.π1)
      (y.idLeft  _ _ idr.π2) `trans` Data.Product.projIdentity idr
  )
  (\_, _, _, _, f, g, h => cong2 (&&)
      (compAssoc x _ _ _ _ f.π1 g.π1 h.π1)
      (compAssoc y _ _ _ _ f.π2 g.π2 h.π2)
  )
```

