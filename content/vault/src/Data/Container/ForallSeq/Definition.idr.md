<!-- idris
module Data.Container.ForallSeq.Definition

import Data.Container.Definition
import Data.Container.Morphism.Definition
import Data.Container.Extension
import Data.Sigma

-- The new one
public export
-->

### Sequencing Action / Universal Composition

This operator is defined in the same way as
$a \rhd b$ but uses a Π-type instead of Σ. While existential composition is a
monoidal product, universal composition is an action \defref{def:action}.

```idris
(▶) : Container -> Container -> Container
(▶) c1 c2 = (x : Ex c1 c2.req) !>
            ((val : c1.res x.ex1) -> c2.res (x.ex2 val))
```

