
### Poly, the Category of Polynomial functors

The study of containers is closely linked to the study of polynomial functors
while the category $\mathcal{Cont}$ and $\mathcal{Poly}$ are the same,  their
roots and motivations are different. Some insight comes from combining both
interpretation, and so it is important to know the difference, especially when
it comes to interpreting each as the foundation for interactive programs.

Indeed, $\mathcal{Poly}$, just like $\mathcal{Cont}$ is also used in the context
of interactive programs. The most exciting work is currently put forward by The
Topos institute and the chief publication in that regard is the _Poly book_ By
David Spivak and Nelson Niu.

In this book, the category $\Poly$ is presented as a tool to represent wiring
diagrams, in turn, those diagrams can be instanciated into dynamical systems
that can change across their lifetime and faithfully represent real-world
scenarios.

The category of polynomial functors is given by a set of positions, and a set of
directions, from which we can move.

<!-- idris
module Thesis.Poly

import Data.Product
import Data.Coproduct
-->

One intuition that could be given for the name would be to borrow from a
physical simulation system that can produce a new position
resulting from applying the direction vector at the given position.

There are other names for those concepts that come from other intuitions,
for example, in a game-theoretic interpretation, the positions would be the
_arena_ and the directions are the _moves_. The arena gives the set of possible
states that an agent can be in and from a given state, the agent has a set of
possible _moves_ it can go towards. Like before, the system becomes dynamical
when there is a way to recover a new state after selecting a move. We call this
way of turning a position/direction pair into one dynamical system "giving
dynamics to the string diagram"


### Dynamical systems - Moore & Mealy Machines

An example of a dynamical system are finite state machines. They store an internal
state, behave differently on input depending on that internal state, and some inputs
can change that internal state. Additionally, finite state machines can be composed
in multiple ways by running in parallel or in sequence for example. All those
behaviours can be captured with a term in $\Poly$ and it is the topic of this section.

Moore machines are given by three sets and two functions:

- $S$ the set of states.
- $O$ the set of outputs.
- $I$ the set of inputs.
- $\mathit{return} : S → O$ the function extracting the current output from the state
- $\mathit{update} : S × I → S$ the transition function from a current state and an
  input to a new state.

By taking the functions $\mathit{return}$ and $\mathit{update}$ as values to the
`MkPolyMap` constructor we can build the dependent lens $Poly((S, S), (O, I))$.

```idris
record Mealy (s, i, o : Type) where
  constructor MkMealy
  return : s -> o
  update : s -> i -> s

MealyLens : Mealy s i o -> MkPoly s (const s) `PolyMap` MkPoly o (const i)
MealyLens (MkMealy r u) = MkPolyMap r u
```

In this definition, the codomain of the lens is the interface to the mealy machine.
What's more, the first projection of the polynomial is the output and the second is the input.
This relation is flips the intput/output relation from my approach to dependent lenses as interactive
systems.

The basic state machine above can be represented with the container $(Nat,Move)$
but this description is not enough to obtain the execution profile of the state
machine, we still need to _give it dynamics_. We do this by building a morphism
of containers $(State, State) \Rightarrow (Nat, Move)$, it is defined by two
functions $State \to Nat$ and $State \times Move \to State$. Those two functions
also determine a state machine with state $State$, input $Move$ and outputs
$Nat$. Therefore, this encoding of dynamical system plases the input of the
system in the _direction_ (or the _indexed_ part of the container), and the
output in the _positions_ (or the _base_ of the container).


### Composing Mealy Machines

The previous definition is interesting in that it gives an account of state machines
in terms of lenses, but does not make use of this insight to augment the power of
state machines. Crucially, due to the semantic asymmetry of mealy machines having
state on the domain and input/output on the codomain, we cannot compose it with
other mealy machines, we can only compose them using either "state transformers" or
"input/output transformer" but neither are mealy machines themselves.

To address this we define _composable mealy machines_ as the para-construction

- [ ] link to para construction

of the lens by turning the state into a _parameter_ and defining mealy-machine
composition as para-composition where the parameter is combined using the monoidal
product used for the parametrisation, in this case, Tensor.


