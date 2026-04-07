<!-- idris
module Data.Container.Closed.Definition

import Data.Container.Definition

import Data.Sigma
-->

The lenses here are "closed" in the sense of cartesian closure, since they are defined using a single function. Where before we had a dependent lens be defined by two map $fwd : a → b$ and $bwd : (x : a) → b' (fwd\ x) → a'\ x$,
closed lenses refactor the common argument and make use of  a continuation to
obtain the resulting $a'\ x$ value: $(x : a) → Σ (y : b). (b'\ y → a'\ x)$. Here is the idris implementation:

````definition {label="def:closed-lens"}
A closed lens between containers $(A, \bar{A})$ and $(B, \bar{B})$ is a function $(a : A) → Σ (b : B) . \bar{B}(b) → \bar{A}(a)$
```idris
public export
record (=&>)(c1, c2 : Container) where
  constructor (!!)
  fn : (x : c1.req) -> Σ (y : c2.req) | c2.res y -> c1.res x
```
````



Just like dependent lenses, closed lenses compose in the way we'd expect. It's worth noting that the performance characteristic of this type are different since we do not need
to recompute the forward part to execute the backward map.

```idris
public export
(|&>) : a =&> b -> b =&> c -> a =&> c
(|&>) x y = !! \z => let r : ?
                         r = x.fn z
                         s : ?
                         s = y.fn r.π1
                      in s.π1 ## r.π2 . s.π2
```

Closed lenses also have  an identity.

```idris
public export
identity : (0 a : Container) -> a =&> a
identity _ = !! \x => x ## id
```
