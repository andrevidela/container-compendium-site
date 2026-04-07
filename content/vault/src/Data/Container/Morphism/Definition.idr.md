<!-- idris
module Data.Container.Morphism.Definition

import Data.Container.Definition
import public Data.Category.Ops
import Control.Order
import Control.Relation

||| A container morphism
public export
-->

### $\Cont$ the Category of Containers and Dependent Lenses

There are many ways of mapping between morphisms,
the one presented here matches the way we think of container morphisms
as _dependent lenses_.

First, a quick refresher on lenses, for more see \secref{plain-lenses-for-programmers}.

A lens, given by boundaries $(a, a'), (b, b')$ is a map $(a, a') → (b, b')$
given by a pair of functions $a → b$ and $a → b' → a'$

If we think of `a` and `b` as "queries", and `a'` and `b'` as "responses"
then the first function translates queries `a` to queries `b` and
the second converts back responses of `b'` into responses `a'`.

This intuition interprets lenses as a process that delegates queries
to a subsystem, and translates back subsystem responses into responses
in the original context.

One of the main motivation for dependent lenses come from the coproduct
completion of lenses. Lenses are not closed under coproducts because we
cannot prove that the response given to a coproduct of queries, matches
the query that was sent \secref{lens-coproduct}.

But making it closed under coproduct is not a big change, it suffices
to make the responses dependent on the queries, so that the objects are
some sort of _dependent boundary_, or more colloquially, containers.
The type of such lenses is now indexed over two containers instead of
two boundaries.

```idris
record (=%>) (c1, c2 : Container) where
  constructor (<!)
```

To adapt the definition of lens, we replicate the semantics of the "get"
and "set" maps but on conatiners.

First we map queries to queries, since containers are types in their
first projection, there is no difference with the definition of lenses.

```idris
  fwd : c1.request -> c2.request
```

However, in the backward part, since responses are indexed over queries,
we need to say that the response we got for the subsystem, necessarily
comes from an application of `fwd`. And the corresponding response
in the domain matches the original query.

```idris
  bwd : (x : c1.request) -> c2.response (fwd x) -> c1.response x
```

This definition is exactly the one of a _container morphism_ in the traditional
sense.

```definition
A container morphism between $(A, \bar{A})$ and $(B, \bar{B})$ is a pair of
maps $fwd : A → B$ and $bwd : (a : A) → \bar{B}(fwd(a))→\bar{A}(a)$.
```

<!-- idris
%pair (=%>) fwd bwd

||| Identity of container morphisms
public export
-->

Using the above definition, we can write an identity morphism that does nothing
to the queries and nothing on the responses.

```idris
identity : (0 a : Container) -> a =%> a
identity v = id <! (\_ => id)
```

<!-- idris
||| Composition of container morphisms
public export
-->

Just like lenses, container morphisms compose in the same way.

```idris
(|%>) : a =%> b -> b =%> c -> a =%> c
(|%>) x y =
    (y.fwd . x.fwd) <!
    (\z => x.bwd z . y.bwd (x.fwd z))
```

Equipped with composition and identity, we can tackle more formal definitions like
categories and functors

<!-- idris
public export
Reflexive Container (=%>) where
  reflexive = identity _

public export
Transitive Container (=%>) where
  transitive = (|%>)

public export
Preorder Container (=%>) where
-->
