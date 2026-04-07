<!-- idris
module Data.Container.Extension.Definition

import Data.Container.Definition

||| Extension of a container as a functor, Also interpreted as "existential" monads
public export
-->

## The Extension of Containers

The extension is crucial to understand containers as data descriptors. Given a container `c`, its extension `Ex c : Type -> Type` gives us the type constructor, in the host language, for the data structure that it represents. A typical example is the $List$ container that we will see in the next section.

````definition {label="def:extension"}
Given a container $(A, \bar{A})$, its extension $⟦\_⟧$ is a functor $\Set → \Set$ given by $⟦(A, \bar{A})⟧ = λ x. Σ (a : A). \bar{A}(a) \to x$.

```idris
record Ex (cont : Container) (ty : Type) where
  autobind
  constructor MkEx
  ex1 : cont.req
  ex2 : cont.res ex1 -> ty
```
````

We reproduce this definition in Idris with a record. While we could
use Σ-types as well, creating a new type for this ensure we never confuse the semantics of the extension with a regular Σ-type. The constructor is marked `autobind` such that one can create a value without using a lambda for the second argument.

<!-- idris
%pair Ex ex1 ex2
-->
