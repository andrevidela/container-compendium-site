<!-- idris
module Data.Container.Sequence.Definition

import Data.Container.Definition
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Extension.Definition
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Eq

import Data.Sigma
import Data.Iso

import Proofs

import Data.Category.Bifunctor

public export
-->

### Sequencing Product / Existential Composition

Earlier, we said that containers _describe_ data structures and the extension
is what makes the description take form as a type inside our programming language \secref{the-extension-of-containers}. For
now, we use the extension of container to define the last two operation on containers
`▷` and `▶`. The first one is well known and is called the "substitution product", or
"container composition", and allows one data definition to be embedded inside another.

````definition {label="def:sequence-product"}
The sequencing product of containers $(A,\bar{A}) \rhd (B,\bar{B})$ is given by
$((a,\bar{a}) : \Sigma (a:A). \bar{A}(a) \to B, \Sigma(y:\bar{A}(a)). \bar{B}(\bar{a}(y)))$
```idris
(▷) : Container -> Container -> Container
(▷) a b =
  (x : Ex a b.request) !>
  (Σ (a.response x.ex1) (b.response . x.ex2))
```
````

We call this operation the "existential composition" because the backward part reads like
"there exists $\bar{A}$ such that $\bar{B}$".


```handdrawn-ink
{
	"versionAtEmbed": "0.3.4",
	"filepath": "Ink/Drawing/2025.9.28 - 23.29pm.drawing",
	"width": 500,
	"aspectRatio": 1
}
```

