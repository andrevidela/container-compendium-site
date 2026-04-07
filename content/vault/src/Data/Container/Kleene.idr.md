
<!-- idris
module Data.Container.Kleene

import Data.Container
import Data.Sigma
import Data.Product

import Data.Vect
import Data.Container.Morphism
import Data.Container.Lift
import Data.Container.Coproduct
import Data.Container.Descriptions.Maybe

import Proofs

%default total
-->

## The Kleene Star on Containers

The Kleene star on containers can be conceptualised by the fixpoint noted$\_^* : \Cont → Cont$ and implemented as $x^* = \mu\ y. I + x \rhd y$. Using our query-response intuition, we read this type as a sequence of queries of `x` that depend on the previous query and a corresponding sequence of responses for those queries. We can hard-code a version without fixpoints by provinding types for the forward and the backward part.

```idris
public export
data StarFw : (0 _ : Container) -> Type where
  Done : StarFw c
  More : (x : c.req) -> (c.res x -> StarFw c) -> StarFw c

public export
data StarBw : (0 c : Container) -> StarFw c -> Type where
  StarU : StarBw c Done
  StarM : {0 c : Container} -> {0 x1 : c.req} -> {x2 : c.res x1 -> StarFw c} ->
          (x : c.res x1) -> (StarBw c (x2 x)) ->
          StarBw c (More x1 x2)
```
````definition
The Kleene star on containers
```idris
public export
Star : Container -> Container
Star c = (x : StarFw c) !> StarBw c x
```
````
```idris
public export
singleton : c.req -> StarFw c
singleton x = More x (\_ => Done)
```

