<!-- idris
module Data.Category.Action

import public Data.Category.Monoid
import public Data.Category.Bifunctor
import public Data.Category.NaturalTransformation

%hide Prelude.(&&)
%hide Prelude.Ops.infixl.(*>)

%unbound_implicits off
-->

## Categorical action

The term _action_ first appeared in the context of
_group actions_ which have the form $⊘ : C \times D \to D$ where $D$ is a group and $C$ is a
set. We say that $C$ is _acting_ on $D$ or that $⊘$ is an _action_ of $C$ on $D$.

We can generalise this notion for any category $D$ with a monoidal category $C$ using a bifunctor $\oslash : C \otimes D \to D$ and some coherence conditions.
```definition {label="def:action"}
Given two categories $\cat{C}$ and $\cat{D}$, with $\cat{C}$ being monoidal  $(\otimes, I, α, l, r)$ we say that  $\cat{C}$ acts on $\cat{D}$ if we the following:

- A bifunctor called the action $\oslash : \cat{C} × \cat{D} → \cat{D}$
- A natural isomorphism called the "actor" $a : ∀ x, y ∈ |\cat{C}|, z ∈ |\cat{D}|. (x ⊗ y) \oslash z \Leftrightarrow x \oslash (y \oslash z)$
- A natural transformation neutralising the monoidal unit $e : I \oslash x \Leftrightarrow x$
- There is a commutative pentagon relating $(((x ⊗ y) ⊗ z) \oslash w)$ and $x \oslash (y \oslash (z \oslash w))$ given by $α × id_w;a ; id_x × a = a ; a$
- There is a left unitor: $a ; l \oslash id = e$
- There is a right unitor: $a ; id \oslash e = r \oslash id$

```


```idris
public export
record Action
  {0 o1, o2 : Type} (c : Category o1) (d : Category o2)
  (mon : Monoidal c) where
  constructor MkAction
  action : Bifunctor c d d
```

Equipped with our action we define the `actor` diagram that ensures the relationship
between the monoidal structure of $\cat{C}$ and the bifunctor. It's a little bit hard to follow what `f1` and `f2` are but they are each branch of the diagram in figure \ref{fig:actor-diag}

```tikz {caption="the definition of the actor" label="fig:actor-diag"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\pentagondiagram{
  node top left={\cat{C} × (\cat{C} × \cat{D})},
  node top right={\cat{C} × \cat{D}},
  node mid left={(\cat{C} × \cat{C}) × \cat{D}},
  node bottom left={\cat{C} × \cat{D}},
  node bottom right={\cat{D}},
  arrow top={id_{\cat{C}} \times \oslash},
  arrow left={assocR},
  arrow right={\oslash},
  arrow bottom left={\otimes \times id_{\cat{D}}},
  arrow bottom right={\oslash}
}
\end{document}
```

```idris
  actor : let 0 f1 : (c × (c × d)) ->> d
              f1 = pair (idF c) action ⨾⨾ action
              0 f2 : (c × (c × d)) ->> d
              f2 = assocR ⨾⨾ pair mon.mult (idF d) ⨾⨾ action
           in f1 =~= f2
```

And our unitor diagram ensuring the relationship between the action and the monoidal unit of $\cat{C}$

```tikz {caption="The right unitor diagram for an action"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\providecommand{\unitordiagram}[6]{
  \begin{tikzcd}[ampersand replacement=\&]
    {#1}
    \\ \\
    {#2} \&\& {#3}
    \arrow["{#4}"', from=1-1, to=3-1]
    \arrow["{#5}", from=1-1, to=3-3]
    \arrow["{#6}"', from=3-1, to=3-3]
  \end{tikzcd}
}
\begin{document}
\unitordiagram
  {(x\otimes I)\oslash y}
  {x\oslash (I \oslash y)}
  {x \oslash y}
  {a}
  {r \oslash id}
  {id \oslash e}
\end{document}
```

```tikz {caption="The left unitor diagram for an action"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\providecommand{\unitordiagram}[6]{
  \begin{tikzcd}[ampersand replacement=\&]
    {#1}
    \\ \\
    {#2} \&\& {#3}
    \arrow["{#4}"', from=1-1, to=3-1]
    \arrow["{#5}", from=1-1, to=3-3]
    \arrow["{#6}"', from=3-1, to=3-3]
  \end{tikzcd}
}
\begin{document}
\quad
\unitordiagram
  {(I \otimes x) \oslash y}
  {I \oslash (x \oslash y)}
  {x\oslash y}
  {a}
  {l\oslash id}
  {e}
\end{document}
```

```idris
  unitor : idF d =~= Bifunctor.applyL {a = c} mon.i action
```

This previous definition makes use of natural isomorphisms, but we can also define a notion of _lax action_
that makes use of natural transformations instead, ensuring the conversion only goes one way.

````definition
A lax action is an action using natural transformation instead of natural isomorphisms.
````

<!-- idris
public export
-->
We give a matching idris definition. It is this definition of action that we are going to use for Containers.
```idris
record LaxAction {0 o1, o2 : Type}
  (c : Category o1) (d : Category o2)
  (mon : Monoidal c) where
  constructor MkLaxAction
  laction : Bifunctor c d d
  lactor : let 0 f1, f2 : (c × (c × d)) ->> d
               f1 = pair (idF c) laction ⨾⨾ laction
               f2 = assocR ⨾⨾ pair mon.mult (idF d) ⨾⨾ laction
            in f1 =>> f2
  lunitor : idF d =>> Bifunctor.applyL {a = c} mon.i laction
```

From an action we can obtain a lax-action by only projecting the natural transformations out of the natural isomorphisms.

```proposition
From any action $(⊘, m, u)$, we can derive a lax-action by projecting out one side of the natural isomorphisms $m$ and $u$.
```
<!-- idris
public export
-->

```idris
relax : {0 o1, o2 : Type} -> {c : Category o1} -> {d : Category o2} ->
        {0 mon : Monoidal c} ->
        Action c d mon -> LaxAction c d mon
relax act = MkLaxAction
    { laction = act.action
    , lactor = act.actor.nat
    , lunitor = act.unitor.nat
    }
```

### A Monoidal Category is a Self-Action

A monoidal category is a special case of an action where the acting category is the same as the category being acted upon.
We formalise this idea by introducing monoidal categories as a _self-action_ and derive an action $⊘ : \cat{D} × \cat{D} → \cat{D}$ by simply reusing the monoidal product.

<!-- idris
public export
-->
````proposition
From any monoidal category $\cat{C}$ emerges an action of $\cat{C}$ on itself.
```idris
monoidalSelfAction : {0 cat : Category _} ->
    (mon : Monoidal cat) -> Action cat cat mon
monoidalSelfAction mon = MkAction
  { action = mon.mult
  , actor = mon.alpha
  , unitor = symNT (mon.leftUnitor)
  }
```
````
