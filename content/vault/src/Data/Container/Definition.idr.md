<!-- idris
module Data.Container.Definition

import Data.Boundary
import Data.Category.Ops
import Data.Sigma

public export
-->
# Containers & Their Structures

- containers by Abott and ghani
- talk about descriptions and derivatives by connor
- Talk about poly and topos things


## What is a Container

The name "container" might be a bit misleading. For programmers, it refers to a data structure
that carries other elements. A tree, a list, a dictionnary, all those are "containers", but
what we are looking at here are _polynomial functors_ in the category of types. Concretely,
this means that they _describe_ data structures such as lists and dictionaries. But they
aren't lists or dictionaries themselves.

The definition of containers is deceptively simple. It's a pair of a type and a second
type indexed by the first. Abbott  \cite{abbottCategoriesContainers2003}
writes $(S \rhd P)$ for the container with shapes $S : Set$ and positions $P : S \to Set$, in this work, because we focus on the interactive nature of containers, we are going to call the indexing part the _request_ and the indexed part the _response_.

````definition
A Container is a pair of a type of requests and a type of responses indexed by the request.
```idris
record Container where
  constructor (!>)
  request : Type
  response : request -> Type
```
````

We use a visually similar operator `!>` as a constructor and even allow it to be binding so that we can write `(s : S) !> P s`.

```idris {hidden=""}
%pair Container request response

public export
(.message) : Container -> Type
(.message) c = c.request
public export
(.msg) : Container -> Type
(.msg) c = c.request
public export
(.req) : Container -> Type
(.req) c = c.request
public export
(.res) : (c : Container) -> c.req -> Type
(.res) c = c.response
```

We also define a couple of smart constructors that simplify the declaration of containers.
The first one allows to define a container with a set of responses that does not depend on
the request.

<!-- idris
public export
-->
```idris
(:-) : Type -> Type -> Container
(:-) req res = (x : req) !> res
```

There are a number of container with special meanings, for now we define them
as monoidal units but we will come back to their semantics once we use them for implementing programs.
<!-- idris
public export
-->
````definition
The neutral for tensor and composition.
```idris
I : Container
I = Unit :- Unit
```
````
<!-- idris
public export
-->
````definition
The neutral for products
```idris
One: Container
One = Unit :- Void
```
````

````definition
The neutral for coproducts.
```idris
Zero : Container
Zero = Void :- Void
```
````

````definition
The function associated with running a container
```idris
public export
continuation : Container -> Type
continuation c = (x : c.request) -> c.response x
```
