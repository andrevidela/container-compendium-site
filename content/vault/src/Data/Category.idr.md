## Category Theory in Idris

<!-- idris
module Data.Category

import Decidable.Equality
import public Data.Category.Ops

import public Proofs

%default total

private infixr 7 ~:>
private infixl 5 |:>
%hide Prelude.(|>)
-->

To prove properties of containers we first need to define the structures that
represent those properties. Because we're primarily interested in compositional
structures, the obvious structure to represent is a _category_.

Mathematically speaking, a category
is a quadruple of objects, morphisms on those objects, an identity morphism for each object, and a composition operation
on the morphisms. Additionally, the composition must be associative and the identity acts as a neutral element for composition.
We can write those property down in a traditional mathematical style:

```definition {label="def:category"}
A category $C$ is defined by $obj(C)$, also written $|C|$, the set of objects, $hom(C)$ the set of morphisms. For which
we write $C(x, y) \in hom(C)$ to denote the morphims between objects $x$ and $y$ in category $C$.
Additionally we have:

- The morphism $id : \forall x ∈ obj(C). C(x, x)$ of identities for each object in $C$
- And $\circ : \forall a, b, c \in obj(C). C(b, c) \to C(a, b) \to C(a, c)$ a way to compose morphisms in $C$.
- Evidence that the identity $id : \forall a \in obj(C). C(a, a)$ is neutral with regards to the composition, that is
   $\forall a, b \in obj(C). \forall f \in C(a, b). id_b\circ f = f = f \circ id_a$.
- Evidence that composition is associative given any 3 morphisms
   $\forall a , b, c, d \in obj(C). ∀ f \in C(a, b), g \in C(b, c), h \in C(c, d). h \circ (g \circ f) = (h \circ g) \circ f$.
```

Note that I'm using the words and notations from set-theory, but in dependently-typed programming, we express those as _types_. Therefore, in our implementation, objects will be a _type_, morphisms will be a relation on objects, and equations will be propositional equalities.
Writing the properties in full can be a bit hard to read, displaying those equalities diagrammatically may help in developing an intuition, here are the left and right identity equations:

```tikz {caption="Evidence that $id$ is neutral wrt to composition: $f\circ id = f = id \circ f$"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
& a && a \\
{} \\
& b && b
\arrow["f", from=1-2, to=3-4]
\arrow["{id_a}", from=1-2, to=1-4]
\arrow["f", from=1-4, to=3-4]
\arrow["f"', from=1-2, to=3-2]
\arrow["{id_b}"', from=3-2, to=3-4]
\end{tikzcd}
\end{document}
```

And the composition of morphisms:

```tikz {caption="Evidence that composition is associative $f\circ (g \circ h) = (f \circ g)\circ h$" label="fig:composition-assoc"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
& a && b \\
{} &&& {} \\
&&& c && d
\arrow["{g \circ f}"', from=1-2, to=3-4]
\arrow["f", from=1-2, to=1-4]
\arrow["g", from=1-4, to=3-4]
\arrow["h"', from=3-4, to=3-6]
\arrow["{h \circ g}", from=1-4, to=3-6]
\end{tikzcd}
\end{document}
```

With this, we can write the definition a of category in Idris, including the equations for identity and composition.
For this we create a record indexed over the types of objects
\footnote{Instead of indexing the record by the type of the objects, we could make the objects part of the fields of the record but this makes Idris' instance search less reliable. Giving the type of objects as index helps finding instances more accurately.}
.
<!-- idris
public export
-->

```idris
record Category (o : Type) where
  constructor MkCategory
```

The first field gives the morphisms of the category as a relation on objects.

- [ ] See how hard it would be to change the elaboration of operator fields 🔽

```idris
  0 (~:>) : o -> o -> Type
```

For each object $v \in o$, we have an identity morphism:

```idris
  id : (v : o) -> v ~:> v
```

Given two compatible morphisms, we can compose them:

```idris
  (|:>) : {a, b, c : o} -> (a ~:> b) -> (b ~:> c) -> (a ~:> c)
```

Using the identity above, we need to check it is neutral with regards to composition.

The naming convention is that "idRight" indicates that the identity is the neutral element on the right
of a composition operator. And "idLeft" is used for the neutral on the left of the composition operator.
Those equations are faithfully represented by the diagram in figure~\ref{fig:composition-assoc}.

```idris
  0 idRight : (a, b : o) -> (f : a ~:> b) -> f |:> id b ≡ f
  0 idLeft  : (a, b : o) -> (f : a ~:> b) -> id a |:> f ≡ f
```

Finally, we check that composition is associative:

```idris
  0 compAssoc : (a, b, c, d : o) ->
                (f : a ~:> b) ->
                (g : b ~:> c) ->
                (h : c ~:> d) ->
                f |:> (g |:> h) ≡ (f |:> g) |:> h
```

There are many ways to define a category in a programming language, this is but this one is good enough for implementing the rest of this work. For more ways
of defining categories in programming, I invite you to look at how it can be done in
Haskell https://github.com/sjoerdvisscher/data-category or in Agda https://arxiv.org/abs/2005.07059.

You might have noticed the peculiar choice of operator symbols in the above definition,
this is due to a convention I developed when working with records which contain binary
operators. In Idris, record fields automatically synthesise record projections for those
fields. However, those projections now do not exhibit the arity they need to have to be
useful. The `~:>` operator is used infix in the type signatures but its synthesised
field-projection has type `(~:>) : Category o -> o -> o -> Type`, a function of 3
arguments, rather than two.
Because of this, I define `(~>) : Category o => o -> o -> Type`, a binary operator which
takes the category as an auto-implicit argument, allowing us to use it as expected `a ~> b`.

<!-- idris
public export
-->
```idris
0 (~>) : (cat : Category o) => o -> o -> Type
(~>) = Category.(~:>) cat
```

I've done the same for the composition operator `|>`.

<!-- idris
public export
-->
```idris
(|>) : (cat : Category o) => {a, b, c : o} ->
       a ~> b -> b ~> c -> a ~> c
(|>) = Category.(|:>) cat
```

We can use Idris' named argument syntax to build categories using the following constructor:

<!-- idris
public export
-->
```idris
NewCat :
  (0 objects : Type) ->
  (0 morphisms : objects -> objects -> Type) ->
  (identity : (x : objects) -> morphisms x x) ->
  (composition : {a, b, c : objects} ->
    morphisms a b -> morphisms b c -> morphisms a c) ->
  (0 identity_right : {a, b : objects} -> (f : morphisms a b) ->
      composition f (identity b) ≡ f) ->
  (0 identity_left : {a, b : objects} -> (f : morphisms a b) ->
      composition (identity a) f ≡ f) ->
  (0 compose_assoc : {a, b, c, d : objects} ->
      (f : morphisms a b) -> (g : morphisms b c) -> (h : morphisms c d) ->
      composition f (composition g h) ≡ composition (composition f g) h) ->
  Category objects
NewCat _ m i c ir il a =
  MkCategory m i c (\_, _ => ir) (\_, _ => il) (\_, _, _, _ => a)
```

Now that we have a compete definition, we can start giving some examples of categories. At its core, a category is a structure that composes. So anything that has a well behaved composition operator is a candidate for being a category.


```idris
public export
(.idswap) : (cat : Category o) -> (a, b : o) -> (m : a ~> b) -> (cat.id a |> m) {cat, a, b=a, c=b} ≡ (m |> cat.id b){cat, a, b, c=b}
(.idswap) cat a b m = trans (cat.idLeft {}) (sym $ cat.idRight {})
```

### About the design of the library

There are many choices that oculd have been made differently, for example,  Why index over the object set? if we're indexing, why not also index over the set of morphisms? why rely on built-in equality and not relations? Let's address those questions one by one

#### Why index over the set of objects

This works
```
record Cat (obj : Type) where
  constructor MkC
  mor : Rel obj

(~>) : (c : Cat o) => Rel o
(~>) = c.mor

private infixr 1 ~>


record Func (c : Cat o1) (d : Cat o2) where
  constructor MkF
  mapO : o1 -> o2
  mapH : {0 x, y : o1} -> x ~> y -> mapO x ~> mapO y
```

This does not

```
namespace Fail
 failing "Multiple solutions found"
  record Cat where
    constructor MkC
    obj : Type
    mor : Rel obj

  (~>) : (c : Cat ) => Rel c.obj
  (~>) = c.mor

  private infixr 1 ~>

  record Func (c : Cat ) (d : Cat) where
    constructor MkF
    mapO : c.obj -> d.obj
    mapH : {0 x, y : c.obj} -> x ~> y -> mapO x ~> mapO y
```

Because we want to write `~>` wherever possible, and instance search does not work well with projections, we index over the set of object which gives just enough information to constraint the search space and allow proof search to resolve.

#### Why built-in equality



### The Opposite Category

A common construction in category is taking the dual of a category. This operation
is written as superscript $op$. Here, I will write `.op` to obtain the dual of a category.

<!-- idris
public export
-->

```idris
(.op) : Category o -> Category o
(.op) cat = NewCat
    { objects = o
	  , morphisms = (\x, y => y ~> x)
    , identity = cat.id
    , composition = (\f, g => (|:>) cat g f )
    , identity_left = \f => cat.idRight _ _ f
    , identity_right = \f => cat.idLeft _ _ f
    , compose_assoc = (\f, g, h => sym (cat.compAssoc _ _ _ _ h g f))
    }
```

Unlike Agda-category, we do not require that calling `.op` twice is definitionally equal to the identity.

### The Discrete Category

We can build the discrete category where there is only one morphism per object.
<!-- idris
public export
-->

````definition
The discrete category only has identity morphisms for each object.
```idris
DiscreteCat : Category o
DiscreteCat = NewCat
  { objects = o
  , morphisms = (\x, y => x === y)
  , identity = (\_ => Refl)
  , composition = (\f,g => trans f g)
  , identity_right = (\Refl => Refl)
  , identity_left = (\Refl => Refl)
  , compose_assoc = (\_, _, _ => UIP {})
  }
```
````

### The One-Object Category

There is a category with only one object and one morphism, that is the terminal category, or the one-object category. We use it to write functors that create values out of "nothing" and in this context the one-object category is written $\textit{1}$, and such functors have the shape $\textit{1} → \cat{C}$

<!-- idris
public export
-->
````definition {label="terminal-cat"}
The terminal category with one object and one morphism.
```idris
OneCat : Category Unit
OneCat = NewCat
  { objects = ()
  , morphisms = (\x, y => Unit)
  , identity = (\_ => ())
  , composition = (\_,_ => ())
  , identity_right = (\() => Refl)
  , identity_left = (\() => Refl)
  , compose_assoc = (\_, _, _ => Refl)
  }
```
````

### The Category of Types and functions

Idris types and non-dependent functions form a category. The objects are types, the morphisms are plain functions, functions
compose via traditional function composition. This category is called `Set`

<!-- idris
public export
-->
````definition {label="def:set-cat"}
Types and functions between them form a category $\Set$.
```idris
Set : Category Type
Set = NewCat
  { objects = Type
  , morphisms = (\a, b => a -> b)
  , identity = (\_ => id)
  , composition = (\f, g => g . f)
  , identity_right = (\_ => Refl)
  , identity_left = (\_ => Refl)
  , compose_assoc = (\_, _, _ => Refl)
  }
```
````
This is an example of a program that would require universe levels or cumulativity in order to
be appropriately represented, but given the limitation of the Idris programming language, this definition
has type `Type`.

```idris {hidden=""}
public export
(.obj) : {o : Type} ->  Category o -> Type
(.obj) _ = o
```

