<!-- idris
module Data.Container.Morphism.Context

import Data.Container.Definition
import Data.Container.Morphism.Definition
-->

### Container Contexts

Contextual information is essential to run programs written with containers. We identify two kinds of contextual information, _states_ and _costates_.
This naming scheme is inspired from quantum computing and its string diagram where a state is a left unit and a costate is a right unit.

In the domain of containers, such units are used to "wrap up" computation either by providing inputs to a system or closing out its output by means
of a handler.

#### Container State

A container state is a morphism of type `I =%> a`, which is made up of two morphisms `1 -> a.request` and `1 -> a.response -> 1`. Because
the second one is a map to the terminal object, we can use the terminal map in $Set$ to implement it. The first map is more interesting
because is indicates that a `State` is always able to generate events from a unit input.

<!-- idris
public export
-->
````definition
A _state_ is a map from $I$.
```idris
State : Container -> Type
State a = I =%> a
```
````

Given a `State` one can extract values from it at any point:

<!-- idris
public export
-->
```idris
(.getVal) : State a -> a.request
(.getVal) m = m.fwd ()
```

And given any value, we can use it to create a `State`:

<!-- idris
public export
-->
```idris
state : a.request -> State a
state x = const x <! (const (const ()))
```

#### Container Costate

As the dual of `State`, the `Costate` of a container always returns a response given a message. It's a way to tie up a computation defined as a morphism
by giving it a handler. The word "handler" implies that a costate will provide a valid response for any message sent that follow the specification given by
its container. We can see this in the signature of the morphism `Costate a = a =%> I` where the forward part is a terminal map but the backward part
is isomorphic to `(x : a.request) -> a.response x`.

<!-- idris
public export
-->
````definition
A costate is a map to $I$.
```idris
Costate : Container -> Type
Costate a = a =%> I
```
````

We can obtain the underlying handler from a costate by running it:

<!-- idris
public export
-->
```idris
runCostate : Costate a -> (x : a.request) -> a.response x
runCostate m x = m.bwd x ()
```

And turn any handler into a costate:

<!-- idris
public export
-->
```idris
costate : ((x : a.request) -> a.response x) -> Costate a
costate f = const () <! (\x => const (f x))
```
