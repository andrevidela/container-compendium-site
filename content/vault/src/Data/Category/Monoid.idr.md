<!-- idris
module Data.Category.Monoid

import public Data.Category
import public Data.Category.Bifunctor
import public Data.Category.Iso
import public Data.Category.Product
import public Data.Category.NaturalTransformation


%hide Prelude.Ops.infixl.(*>)
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

%default total
%unbound_implicits off

||| A monoidal category
public export
-->
## Monoidal Category

One of the defining features of $\Cont$ is the plurality of monoidal products within it.
To represent them we give the definition of a monoidal category which we will instanciate
with multiple monoidal product in $\Cont$.

```definition {label="defn:mon-cat"}
A monoidal product on a Category $\cat{C}$ is given by:

- A bifunctor $⊗ : \cat{C} × \cat{C} → \cat{C}$
- An object $I ∈ \cat{C}$
- Natural Isomorphisms:
  - For associativity $α: X ⊗ (Y ⊗ Z) ≅ (X ⊗ Y) ⊗ Z$
  - For units on the left : $λ : X ⊗ I ≅ X$
  - For units on the right : $ρ : I ⊗ X ≅ X$
```

```idris
record Monoidal {0 o : Type} (c : Category o) where
  constructor MkMonoidal

  mult : Bifunctor c c c

  i : o
```

```tikz {caption="The pentagon diagram for a monoidal category}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\pentagondiagram{
  node top left={c × (c × c)},
  node top right={c × c},
  node mid left={(c × c) × c},
  node bottom left={c × c},
  node bottom right={c},
  arrow top={id_c \times \otimes},
  arrow left={assocR},
  arrow right={\otimes},
  arrow bottom left={\otimes \times id_c},
  arrow bottom right={\otimes}
}
\end{document}
```


```idris
  alpha : let f1, f2 : (c × (c × c)) ->> c
              f1 = ((idF _) `pair` mult) ⨾⨾ mult
              f2 = assocR ⨾⨾ ((mult `pair` idF _) ⨾⨾ mult)
          in f1 =~= f2
```

TODO: add diagram

```idris
  leftUnitor :
      let 0 leftAppliedMult : c ->> c
          leftAppliedMult = applyL {a = c, b = c, c} i mult
      in leftAppliedMult =~= idF c
```

TODO: add diagram

```idris
  rightUnitor :
      let 0 rightAppliedMult : c ->> c
          rightAppliedMult = applyR i mult
      in rightAppliedMult =~= idF c
```

```idris {hidden=""}
%unbound_implicits on
public export
```

Like before, we define a couple of utility functions to more easily manipulate
monoidal products. $(×)$ uses the product's bifunctor to combine objects and
$(⊗)$ uses the same functor to combine morphisms.

```idris
(⊗) : {auto 0 cat : Category o} -> (mon : Monoidal cat) => o -> o -> o
(⊗) a b = mon.mult.mapObj (a && b)

public export 0
(-⊗-)  : {auto 0 cat : Category o} -> {0 x, y, a, b : o} -> (mon : Monoidal cat) =>
       x ~> y -> a ~> b -> x ⊗ a ~> y ⊗ b
(-⊗-) m1 m2 = mon.mult.mapHom (x && a) (y && b) (m1 && m2)
```

## Monoids in a Monoidal Category

Given a monoidal category, we define *monoids* in that category by leveraging the
monoidal structure of the category.

```definition
Given a category $\cat{C}$ and $(⊗, I, α, λ, ρ)$ a monoidal product on it. A _monoid object_
with respect to this structure is a triple $(M, μ, η)$ where:

- $M ∈ \cat{C}$ is an object of $\cat{C}$
- $μ : M ⊗ M → M$ combines those objects using the monoidal product from $\cat{C}$
- $η : I → M$ a map from the neutral object of the monoidal product from $\cat{C}$
- And the following equations hold:
  - The pentagon $α ; 1 ⊗ μ ; μ ≅ μ ⊗ 1 ; μ$
  - The left-unit  $η ⊗ 1 ; μ ≅ λ$
  - The right-unit $1 ⊗ η ; µ ≅ ρ$
```

```idris {hidden=""}
%unbound_implicits off
||| a monoid in a monoidal category
public export
```

We port this definition in Idris directly by providing a record with all the necessary
information, parameterised over the category and its monoidal structure.

```idris
record MonoidObject {0 o : Type} {cat : Category o} (mon : Monoidal cat) where
  constructor MkMonObj
  obj : o
  η : mon.i ~> obj
  mult : obj ⊗ obj ~> obj
```
```tikz
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
{i \times x} % top node
{x \times x} % bottom left corner node
{x} % right node
{\nu\times id_x} % left arrow
{\lambda} % diagonal arrow
{\mu} % bottom arrow
\end{document}
```
```idris
  0 left : let 0 η_id_μ, λ : mon.i ⊗ obj ~> obj
               0 topMorphism : mon.i ⊗ obj ~> obj ⊗ obj
               topMorphism = η -⊗- cat.id obj
               η_id_μ = topMorphism |> mult
               λ = mon.leftUnitor.nat.component obj
            in η_id_μ === λ
```
```tikz
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
{x \times i} % top node
{x \times x} % bottom left corner node
{x} % right node
{id_x \times \nu} % left arrow
{\rho} % diagonal arrow
{\mu} % bottom arrow
\end{document}
```
```idris
  0 right : let 0 id_η_μ, ρ : obj ⊗ mon.i  ~> obj
                0 topMorphism : obj ⊗ mon.i  ~> obj ⊗ obj
                topMorphism = cat.id obj -⊗- η
                id_η_μ = topMorphism |> mult
                ρ  = mon.rightUnitor.nat.component obj
             in id_η_μ === ρ
```
```tikz {caption="The pentagon diagram for a monoid}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\pentagondiagram{
  node top left={m × (m × m)},
  node top right={m × m},
  node mid left={(m × m) × m},
  node bottom left={m × m},
  node bottom right={m},
  arrow top={id_c \times mult},
  arrow left={assoc},
  arrow right={mult},
  arrow bottom left={mult \times id_m},
  arrow bottom right={mult}
}
\end{document}
```
```idris
  0 assoc : let
                0 botLeft : (obj ⊗ obj) ⊗ obj ~> obj
                botLeft = mult -⊗- cat.id obj |> mult
                0 assoc : ((obj ⊗ obj) ⊗ obj) ~> obj ⊗ (obj ⊗ obj)
                assoc = mon.alpha.tan.component (obj && (obj && obj))
                0 topRight : ((obj ⊗ obj) ⊗ obj) ~> obj
                topRight = assoc |> cat.id obj -⊗- mult |> mult
            in botLeft === topRight
```
