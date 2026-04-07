<!-- idris
module Data.Category.Functor

import public Data.Category

import Syntax.PreorderReasoning

import Proofs

%hide Prelude.Functor
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
%hide Prelude.Ops.infixl.(*>)

%unbound_implicits off

public export
-->

## Functors

Categories hold the compositional structure of objects and morphisms. But just
like any other structure, we are also interested in maps _between_ them. In this
case, a mapping between two categories $\cat{C}, \cat{D}$ is given by a map on their objects
$\textit{mapObj} : |\cat{C}| → |\cat{D}|$[^objectset] and a map on morphisms
$\textit{mapHom} : \forall x, y \in |\cat{C}|. \cat{C}(x, y) \to \cat{D}(\mathit{mapObj}(x), \mathit{mapObj}(y))$.
Such mapping is called a _functor_, we can represent it as a record
holding both maps.

```definition {label="def:functor"}
A Functor $F$ between categories $\cat{C}$ and $\cat{D}$ is given by a map on objects $f : |\cat{C}| → |\cat{D}|$
and a map on morphisms $\mor{C}{x}{y} → \mor{D}{f(x)}{f(y)}$ such that:

- Mapping the identity results in the identity in the target category $F(id_C) ≅ id_D$ .
- Mapping a composite is like composing after mapping each individual morphism $∀ m \in \mor{C}{x}{y}, n ∈ \mor{C}{y}{z}. F(m ; n) ≅ F(m) ; F(n)$
```

We use the convention that functors themselves are always written using capital letters, and their map on objects in lowercase. For the map on morphisms we use the name of the functor as an uppercase letter. To recap, for a functor $F$, it has a map on morphism $f$ (lower case), and a map on morphism $F$ (capital case).

The implementation of functors follows directly its mathematical definition, first
we parameterise our definition by the domain and codomain categories, and give as
fields the map on objects and the map on morphisms.

```idris
record (->>) {0 o1, o2 : Type} (c : Category o1) (d : Category o2) where
  constructor MkFunctor

  -- A way to map objects
  mapObj : o1 -> o2

  -- A way to map morphisms
  -- For each morphism in C between objects x and y
  -- we get a morphism in D between the corresponding objects x and y
  -- but mapped to their counterparts in d
  mapHom : (x, y : o1) -> x ~> y -> mapObj x ~> mapObj y
```

In addition to the maps themselves, we need to ensure the map on morphism preserves
identity. That is, an identity arrow in the source category needs to map to an
identity arrow in the target category. Using the categories $\cat{C}, \cat{D}$ defined
above, we need to ensure that $\textit{mapHom}(id_{\cat{C}}) \equiv id_{\cat{D}}$

```idris
  -- mapping the identity morphism in C results in the identity morphism in D
  0 presId : (v : o1) -> mapHom v v (c.id v) = d.id (mapObj v)
```

Finally, the map on morphism needs to preserve composition, such that, given
two maps $f : \cat{C}(x, y)$ and $g : \cat{C}(y, z)$ for three objects
$x, y, z \in |\cat{C}|$ we can compose their maps in $\cat{D}$
$\textit{mapHom}(f);_{\cat{D}} \textit{mapHom}(g)$ in a way that coincides with composing the morphisms in
$\cat{C}$ and mapping the result into $\cat{D}$, $\textit{mapHom}(f ;_c g)$. We
can show this relation in the triangular diagram \figref{fig:functor-hom}, which we add as a field to our `Functor` record.

```tikz {label="fig:functor-hom" caption="The commutative diagram for the fact that mapHom preserves composition"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{mapObj(x)} && {mapObj(y)} \\
\\
& {mapObj(z)}
\arrow["{mapHom(f)}", from=1-1, to=1-3]
\arrow["{mapHom(f ; g)}"', from=1-1, to=3-2]
\arrow["{mapHom(g)}", from=1-3, to=3-2]
\end{tikzcd}
\end{document}
```

Note that this is our first use of a _lifted let-binder_ \secref{let-binding} in a type signature.

```idris
  0 presComp :
    (x, y, z : o1) -> -- given three objects x, y, z
    (f : x ~> y) ->   -- a morphism x -> y
    (g : y ~> z) ->   -- and a morphism y -> z

    let 0 f1, f2 : mapObj x ~> mapObj z
        -- Mapping the morphism after composition
        f1 = mapHom x z (f |> g)
        -- And composing the maps of each morphism
        f2 = mapHom x y f |> mapHom y z g
    in f1 === f2 -- Are the same thing
```

Functors compose in the expected way, that is, if we have a functor $F : \cat{C} \to \cat{D}$ and $G : \cat{D} \to \cat{E}$ then we can compose them such that
their composite is $F ⨾⨾ G : \cat{C} \to \cat{E}$.
<!-- idris
public export
-->
```idris
(⨾⨾) : {0 o1, o2, o3 : Type} -> {0 a : Category o1} -> {0 b : Category o2} -> {0 c : Category o3} ->
      a ->> b -> b ->> c -> a ->> c
(⨾⨾) f1 f2 = MkFunctor
  (f2.mapObj . f1.mapObj)
  (\a, b, m => f2.mapHom (f1.mapObj a) (f1.mapObj b) (f1.mapHom a b m))
  (\x => cong (f2.mapHom (f1.mapObj x) (f1.mapObj x)) (f1.presId x)
        `trans` f2.presId (f1.mapObj x))
  (\a, b, c, h, j =>
      cong (f2.mapHom (f1.mapObj a) (f1.mapObj c)) (f1.presComp a b c h j) `trans`
      f2.presComp _ _ _ (f1.mapHom a b h) (f1.mapHom b c j))
```

While this helper function is not strictly necessary for defining functors, we use it as a helper instead of `mapHom`.
The name is a reference to the function `fmap` in Haskell.

```idris {hidden=""}
public export
```

```idris
fmap : {0 o1, o2 : Type} ->
       {c1 : Category o1} -> {c2 : Category o2} -> {f : c1 ->> c2} ->
       {a, b : o1} ->
       a ~> b -> f.mapObj a ~> f.mapObj b
fmap x = mapHom f a b x
```

With this basic definition we can build a couple of interesting functors, the first one is
the identity functor. This functor maps a category to itself.

```idris {hidden=""}
public export
```

````definition
The identity functor maps a category to itself.
```idris
idF : {0 o : Type} -> (0 c : Category o) -> c ->> c
idF c = MkFunctor id (\_, _ => id) (\_ => Refl) (\_, _, _, _, _ => Refl)
```
````

Another interesting functor is the functor from the discrete category to
any category given one of its objects. Think of it as the function `() -> a`
given `x : a`.

```idris {hidden=""}
public export
```
````definition
The constant functor maps the terminal category to the category $\cat{C}$ by using an object $o ∈ |\cat{C}|$ as a constant codomain.
```idris
Const : {0 o : Type} -> o -> (c : Category o) -> OneCat ->> c
Const x c = MkFunctor
    (const x) (\_, _, _ => c.id x) (\_ => Refl)
    (\_, _, _, _, _ => sym $ c.idLeft _ _ (c.id x) )
```
````
<!-- idris
public export
-->

Functors in the opposite category

```idris
(.op) : {0 a, b : _} -> a ->> b -> a.op ->> b.op
(.op) func = MkFunctor
    func.mapObj
    (\a, b => func.mapHom b a)
    func.presId
    (\x, y, z, f, g => func.presComp z y x g f)
```

```idris
public export
record FullyFaithful {o1, o2 : Type} {c : Category o1} {d : Category o2} (f : c ->> d) where
  constructor MkFullFaithful
  inv : {x, y : o1} -> f.mapObj x ~> f.mapObj y -> x ~> y
  0 inv1 : {x, y : o1} -> (m : x ~> y) -> inv {x, y} (f.mapHom x y m) ≡ m
  0 inv2 : (x, y : o1) -> (m : f.mapObj x ~> f.mapObj y) -> f.mapHom x y (inv {x, y} m) ≡ m
```


[^objectset]: The $|\cat{C}|$ syntax denotes the object set of the category as written in definition \ref{def:category}.
