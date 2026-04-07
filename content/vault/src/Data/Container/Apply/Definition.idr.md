<!-- idris
module Data.Container.Apply.Definition

import Data.Container.Definition
-->

## Functorial Application and Monadic Lenses

Functorial application combines a functor $F ∈ \Set → \Set$ with a container by applying
the functor to the the "response" part of the container.

<!-- idris
public export
-->
````definition
Functor application of containers, read "app".
```idris
(•) : (f : Type -> Type) -> Container -> Container
(•) f c = (x : c.req) !> f (c.res x)
```
````

The first thing to notice about this operator is that it flips the arrows between
the functor category in $\Set$ and the functor category in $\Cont$. Formally this
is described as a functor from the opposite category of endofunctors to the category
of morphisms in $\Cont$. Or equivalently:
