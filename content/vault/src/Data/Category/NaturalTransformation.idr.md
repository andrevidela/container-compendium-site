## Natural transformations

Functors are the tools to relate two categories, in turn natural transformations are the tool to relate two functors.

<!-- idris
module Data.Category.NaturalTransformation

import public Data.Category.Functor
import public Data.Category.Iso
import public Data.Category.Notation
import public Data.Category.Proofs
import Data.Category.Bifunctor

import Data.Iso.Category

import Control.Category as Cat

import Syntax.PreorderReasoning
import Control.Relation
import Control.Order

import Proofs.Congruence
import Proofs.DSL
import Proofs.Extensionality
import Proofs.UIP

%hide Prelude.Functor
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

%hide Pipeline.Equality.infixr.(>|)
private infixr 7 >|

%unbound_implicits off
-->

A natural transformation is a relation between two _functors_ between two categories. Let's call them $f$ and $g$ and say they are between categories $\mathcal{C}$ and $\mathcal{D}$. We're going to say that they have maps on objects $f : \mathcal{C} \to\mathcal{D}$ and $g : \mathcal{C} \to\mathcal{D}$, as well as maps on morphisms $F: \mathcal{C}(x, y) \to\mathcal{D}(f(x), f(y))$ and $G: \mathcal{C}(x, y) \to\mathcal{D}(g(x), g(y))$.

A natural transformation is defined primarily by its _component_ which says that for each object in $\mathcal{C}$ we obtain a morphism in $\mathcal{D}$ by using the map on object from functors $f$ and $g$, we call the component $\varphi$. More succinctly we write $\varphi : \forall x \in |\mathcal{C}|. \mathcal{D}(f(x), g(x))$.

We can already start writing this definition in Idris using a record, we are going to use the symbol `==>>` for natural transformations, it is meant to represent a thick arrow.

<!-- idris
public export
-->
````definition {label="def:natural-transformation"}
Given two functors $F, G : \cat{C}\to\cat{D}$, a natural transformation $F \Rightarrow G$ is given by:

- A component $\varphi : ∀ x \in |\cat{C}|. \mor{D}{f(x)}{g(x)}$
- For all morphisms $m ∈ \mor{C}{x}{y}$, the commuting square $F(m);\varphi_y ≡ \varphi_x ; G(m)$
````

- [ ] Fix how the arrow is rendered in latex

```idris
record (=>>) {0 cObj, dObj : Type} {0 c : Category cObj} {0 d : Category dObj}
             (f, g : c ->> d) where
  constructor MkNT
  component : (v : cObj) -> f.mapObj v ~> g.mapObj v
```

In the above you see that each natural transformation needs two functors, and each of them require two categories. The component is defined as a morphism in the category `d` resulting from mapping the object `v` using both `f` and `g`.

The definition does not end here because we also need to make sure that the component respects the map on morphism from each functor. For this, we ensure that each morphism in $\mathcal{C}$ applied to $g$ can be pre-composed with the components, or post-composed and applied to the functor $f$, for the same result. That is $\forall m ∈ \mor{C}{x}{y}. F(m);\varphi_y ≡ \varphi_x ; G(m)$, we can represent it with the following commutative diagram.

```tikz {caption="Naturality square" label="fig:nat-square"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
x \ar[d, "m" left] & f(x) \ar[r, "\varphi_x" above]
         \ar[d, "F(m)" left] & g(x) \ar[d, "G(m)" right] \\
y & f(y) \ar[r, "\varphi_y" below] & g(y)\\
\end{tikzcd}
\end{document}
```

It is left to translate this diagram into a field for our idris definition. As the diagram suggests, we need two objects in $\mathcal{C}$ as the source and target of a morphism $m$ in $\mathcal{C}$, and using, we ensure that the equation holds.

```idris
  0 commutes : (0 x, y : cObj) -> (m : x ~> y) ->
      let -- We build each side of the naturality square
          0 top : f.mapObj x ~> g.mapObj x
          top = component x

          0 bot : f.mapObj y ~> g.mapObj y
          bot = component y

          0 left : f.mapObj x ~> f.mapObj y
          left = f.mapHom _ _ m

          0 right : g.mapObj x ~> g.mapObj y
          right = g.mapHom _ _ m

          -- And the compose them.
          0 comp1 : f.mapObj x ~> g.mapObj y
          comp1 = top |> right

          0 comp2 : f.mapObj x ~> g.mapObj y
          comp2 = left |> bot
      in comp1 === comp2
```

The simplest natural transformation we can build is the identity natural
transformation. Given a functor `f : c -> d` we can build the identity natural
transformation using `f` on the identity morphism in `c`.

<!-- idris
public export
-->
```idris
identity : {0 o1, o2 : Type} -> {c : Category o1} -> {0 d : Category o2} ->
           {f : c ->> d} -> f =>> f
identity = MkNT
  (\x => f.mapHom x x (c.id x))
  (\x, y, m => let
      0 steps : CongPipeline ? (f.mapObj x ~> f.mapObj y)
      steps = (fmap (c.id x)  |> fmap m)
              :: AddNest (f.mapHom x y)
                [ (c.id x |> m)
                , m
                , (m |> c.id y)]
                [ fmap m |> fmap (c .id y) ]
      in runProof steps
          [ sym (presComp f x x y (c.id x) m),
          c.idLeft _ _ m,
          sym (c.idRight _ _ m),
          presComp f x y y m (c.id y)]
  )
```

We also define an equality relation on natural transformation, this is useful
to perform higher-level equalities for example when defining the category of
functors and natural transformations. In particular, two natural
transformations are equal when their components are equal for all inputs.

````definition
Equality of natural transformations is given by equality of their component.
```idris
public export
record NTEq
  {0 o1, o2 : Type}
  {0 c : Category o1} {0 d : Category o2}
  {f, g : c ->> d} (n1, n2 : f =>> g) where
  constructor MkNTEq
  0 sameComponent : (v : o1) -> n1.component v === n2.component v
```
````
```idris {hidden=""}
public export
```
````proposition
We can convert from natural transformation equality to propositional equality.
```idris
0 ntEqToEq :
  {0 o1, o2 : Type} ->
  {c : Category o1} -> {d : Category o2} ->
  {f, g : c ->> d} -> {n1, n2 : f =>> g} ->
  NTEq n1 n2 -> n1 === n2
ntEqToEq (MkNTEq sameComponent) {n1 = MkNT n1 p1} {n2 = MkNT n2 p2} =
  cong2Dep0
    {t3 = f =>> g}
    MkNT
    (funExtDep $ sameComponent)
    (funExtDep0 $ \x => funExtDep0 $ \y => funExtDep $ \z => UIP _ _)
```
````

One of the main feature of natural transformation is that they can be composed in two different ways.

Vertical composition of natural transformations stiches two natural transformation `n : f =>> g` and `m : g =>> h`
and produces a single natural transformation `(n ⨾⨾⨾ m) : f =>> h`. Here `f`, `g`, and `h`, are all functors `c -> d`.

```idris {hidden=""}
public export
```

````proposition
Given two categories $\cat{C}$ and $\cat{D}$ and functors $F, G, H : \cat{C} \to\cat{D}$,and natural transformations $n: F \Rightarrow G$ and $m : G \Rightarrow H$, we can obtain
a natural transformation $n \mathbin{;_v} m: F \Rightarrow H$ by composing the components of $n$ and $m$, and composing their naturality squares.
````

We can represent this notion of composition with the diagram on figure \ref{fig:vertical-comp}, which also illustrates the "verticality" of this notion of composition.

```tikz {caption="Vertical composition of natural transformation." label="fig:vertical-comp"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
C && D
\arrow[""{name=0, anchor=center, inner sep=0}, "G"{description}, from=1-1, to=1-3]
\arrow[""{name=1, anchor=center, inner sep=0}, "F"{description}, shift left=2, from=1-1, to=1-3, bend right=-60]
\arrow[""{name=2, anchor=center, inner sep=0}, "H"{description}, shift right=2, from=1-1, to=1-3, bend right=60]
\arrow["n"', shorten >=0.15cm, shorten <=0.15cm, Rightarrow, from=1, to=0]
\arrow["m"', shorten >=0.15cm, shorten <=0.15cm, Rightarrow, from=0, to=2]
\end{tikzcd}
\end{document}
```

```idris
(⨾⨾⨾) :
  {0 cObj, dObj : Type} ->
  {0 c : Category cObj} -> {d : Category dObj} ->
  {f, g, h : c ->> d} ->
  f =>> g -> g =>> h -> f =>> h
(⨾⨾⨾) nat1 nat2 =
  let
    newComponent : (v : cObj) -> f.mapObj v ~> h.mapObj v
    newComponent x = nat1.component x |> nat2.component x

    0 compProof : (0 x, y : cObj) -> (m : x ~> y) ->
      let 0 n1, n2 : f.mapObj x ~> h.mapObj y
          n1 = f.mapHom x y m |> (nat1.component y |> nat2.component y)
          n2 = (nat1.component x |> nat2.component x) |> h.mapHom x y m
      in n2 === n1
    compProof x y m =
      sym (d.compAssoc {}) `trans`
      glueSquares (nat1.commutes x y m) (nat2.commutes x y m)
  in MkNT newComponent compProof
```


The second way of composing natural transformation requires 2 pairs of functors
that can compose functors end to end. For example, given functors $F_1 : \cat{C_1}\to\cat{D_1}$ and $G_1 : \cat{D_1}\to\cat{E_1}$ as well
as $F_2 : \cat{C_2}\to\cat{D_2}$ and  $G_2 : \cat{D_2}\to\cat{E_2}$ (where $\cat{C_1}, \cat{C_2},\cat{D_1},\cat{D_2},\cat{E_1},\cat{E_2}$ are all categories), and
two natural transformations $n : F_1 \Rightarrow F_2$ and $m : G_1 \Rightarrow G_2$, then we can compose them to obtain
the natural transformation $n * m : G_1\circ F_1 \Rightarrow G_2\circ F_2$ where $\circ$ is functor composition.

````proposition
Horizontal composition is obtained given the following:

- Categories $\cat{C}_1, \cat{C}_2, \cat{D}_1, \cat{D}_2, \cat{E}_1, \cat{E}_2$
- Functors
  - $F_1 : \cat{C_1}\to\cat{D_1}$
  - $G_1 : \cat{D_1}\to\cat{E_1}$
  - $F_2 : \cat{C_2}\to\cat{D_2}$
  - $G_2 : \cat{D_2}\to\cat{E_2}$
- Natural transformations $n : F_1 \Rightarrow F_2$ and $m : G_1 \Rightarrow G_2$

Then we can compose $n$ and $m$ by composing their functors to obtain $n \hcomp m$
````

<!-- idris
public export
-->
```idris
-- Operator for horizontal composition
(-⨾-) : {0 o1, o2, o3 : Type} ->
        {0 a : Category o1} -> {0 b : Category o2} -> {c : Category o3} ->
        {l, k : a ->> b} ->
        {g, h : b ->> c} ->
        k =>> l ->
        g =>> h ->
        k ⨾⨾ g =>> l ⨾⨾ h
(-⨾-) nt1 nt2  =
  MkNT (\v => nt2.component (k.mapObj v) |> h.mapHom (k.mapObj v) (l.mapObj v) (nt1.component v))
  -- proof in appendix
```
```idris {hidden=""}
    (\x, y, m => let
        0 H : {0 a : o2} -> {0 b : o2} ->
              a ~> b -> (h.mapObj a) ~> (h.mapObj b)
        H = h.mapHom _ _
        0 L : {0 a : o1} -> {0 b : o1} ->
              a ~> b -> (l.mapObj a) ~> (l.mapObj b)
        L = l.mapHom _ _
        0 G : {0 a : o2} -> {0 b : o2} ->
              a ~> b -> (g.mapObj a) ~> (g.mapObj b)
        G = g.mapHom _ _
        0 K : {0 a : o1} -> {0 b : o1} ->
              a ~> b -> (k.mapObj a) ~> (k.mapObj b)
        K = k.mapHom _ _
        n2 : ?
        n2 = nt1.component
        n1 : ?
        n1 = nt2.component
        0 n1p : ?
        n1p = nt2.commutes
        0 n2p : ?
        n2p = nt1.commutes
      in Calc $
      |~ ((n1 (k.mapObj x) |> H (n2 x)) |> H (L m))
      ~~ (n1 (k.mapObj x) |> (H (n2 x) |> H (L m))) ..<(c.compAssoc _ _ _ _ (n1 (k.mapObj x)) (H (n2 x)) (H (L m)))
      ~~ (n1 (k.mapObj x) |> (H (n2 x |> L m)))     ..<(cong (n1 (k.mapObj x) |> ) (h.presComp _ _ _ (n2 x) (L m)))
      ~~ (G (n2 x |> L m) |> n1 (l.mapObj y))       ...(n1p (k.mapObj x) (l.mapObj y) (n2 x |> L m))
      ~~ (G (K m |> n2 y) |> n1 (l.mapObj y))       ...(cong (\xn => G xn |> n1 (l.mapObj y)) (n2p _ _ m))
      ~~ ((G (K m) |> G (n2 y)) |> n1 (l.mapObj y)) ...(cong (\x => x |> n1 (l.mapObj y)) (g.presComp _ _ _ (K m) (n2 y)))
      ~~ (G (K m) |> (G (n2 y) |> n1 (l.mapObj y))) ..<(c.compAssoc _ _ _ _ (G (K m)) (G (n2 y)) (n1 (l.mapObj y)))
      ~~ (G (K m) |> (n1 (k.mapObj y) |> H (n2 y))) ..<(cong (G (K m) |> ) (n1p _ _ (n2 y))))
```

Whiskering is the ability to precompose, or postcompose, the same functor to the source
and target of a natural transformation. Precomposing a functor `f` to a natural transformation `g =>> h`
is called "left whiskering" and results in a natural transformation `(f ⨾⨾ g) =>> (f ⨾⨾ h)`.

Postcomposing a functor `f` to a natural transformation `g =>> h` is called "right whiskering" and results in
a natural transformation `(g ⨾⨾ f) =>> (h ⨾⨾ f)`. Both whiskerings are obtained as a special case of horizontal
composition, namely, horizontal composition with the identity natural transformation.

<!-- idris
%hide Cat.Category
public export
-->
```idris
(⨾-) : {a : Category _} -> {b : Category _} -> {c : Category _} ->
       (f : a ->> b) -> {g, h : b ->> c} ->
       g =>> h -> (f ⨾⨾ g) =>> (f ⨾⨾ h)
(⨾-) f n = identity {f}  -⨾- n
```
<!-- idris
public export
-->
```idris
(-⨾) : {0 b : Category _} -> {c : Category _} -> {d : Category _} ->
       {g, h : b ->> c} ->
       g =>> h -> (f : c ->> d) -> (g ⨾⨾ f) =>> (h ⨾⨾ f)
(-⨾) n f = n -⨾- identity {f}
```

````lemma
Given functors $F_1, G_1, H_1 : \cat{C} \to \cat{D}$ and $F_2, G_2, H_2 : \cat{D} \to\cat{E}$ and natural transformations:

- $m_1 : F_1 \Rightarrow G_1$
- $m_2 : F_2 \Rightarrow G_2$
- $n_1 : G_1 \Rightarrow H_1$
- $n_2 : G_2 \Rightarrow H_2$

Then we define the interchange property that relates horizontal and vertical composition with the two ways
of obtaining a natural tranformation $F_1;F_2 \Rightarrow H_1;H_2$

$(m_1\hcomp n_1);_v(m_2 \hcomp n_2) = (m_1\vcomp m_2)\hcomp (n_1\vcomp n_2)$
````

```idris
public export
interchange :
   {c, d, e : Category _} ->
   {f1, g1, h1 : c ->> d} ->
   {f2, g2, h2 : d ->> e} ->
   (m1 : f1 =>> g1) ->
   (m2 : f2 =>> g2) ->
   (n1 : g1 =>> h1) ->
   (n2 : g2 =>> h2) ->
   NTEq ((m1 -⨾- m2) ⨾⨾⨾ (n1 -⨾- n2)) ((m1 ⨾⨾⨾ n1) -⨾- (m2 ⨾⨾⨾ n2))
-- Proof in appendix
```

```idris {hidden=""}
interchange m1 m2 n1 n2 = MkNTEq $ \z =>
    let m1c : (x : _) -> f1.mapObj x ~> g1.mapObj x
        m1c = m1.component
        m2c : (x : _) -> f2.mapObj x ~> g2.mapObj x
        m2c = m2.component
        n1c : (x : _) -> g1.mapObj x ~> h1.mapObj x
        n1c = n1.component
        n2c : (x : _) -> g2.mapObj x ~> h2.mapObj x
        n2c = n2.component
        steps : CongPipeline ? ((f1 ⨾⨾ f2).mapObj z ~> (h1 ⨾⨾ h2).mapObj z)
        steps =
                ((m1 -⨾- m2) ⨾⨾⨾ (n1 -⨾- n2)).component z
             :: ((m1 -⨾- m2).component z |> (n1 -⨾- n2).component z)
             :: ((m2c (f1.mapObj z) |> fmap (m1c z)) |> (n1 -⨾- n2).component z)
             :: ((m2c (f1.mapObj z) |> fmap (m1c z)) |> (n2c (g1.mapObj z) |> h2.mapHom _ _ (n1c z)))
             :: Cong (|> h2.mapHom _ _ (n1c z))
                     ( (((m2c (f1.mapObj z) |> g2.mapHom _ _ (m1c z)) |> n2c (g1.mapObj z)))
                     :: Cong (m2c (f1.mapObj z) |>)
                             [ (g2.mapHom _ _ (m1c z) |> n2c (g1.mapObj z))
                             , (n2c (f1.mapObj z) |> h2.mapHom _ _ (m1c z))]
                     >| [((m2c (f1.mapObj z) |> n2c (f1.mapObj z)) |> h2.mapHom _ _ (m1c z))]
                     )
             >| Cong ((m2c (f1.mapObj z) |> n2c (f1.mapObj z)) |>)
                    [ (h2.mapHom _ _ (m1c z) |> h2.mapHom _ _ (n1c z))
                    , ((h2.mapHom _ _ (m1c z |> n1c z)))]
             >| [((m1 ⨾⨾⨾ n1) -⨾- (m2 ⨾⨾⨾ n2)).component z]
  in runProof steps
  [Refl , Refl , Refl
  , e.compAssoc {}
  , sym (e.compAssoc {})
  , sym (n2.commutes {})
  , e.compAssoc {}
  , sym (e.compAssoc {})
  , sym (h2.presComp {})
  , Refl]
```

#### Natural Isomorphisms

Natural transformations give us a notion of "mapping" for functors, this notion can be extended to be stronger
requiring it to work in both directions. Such definition would require that the component of a natural transformation to be a bijection
```idris {hidden=""}
public export
```
```idris
record (=~=)
  {0 o1, o2 : Type}
  {0 c : Category o1} {0 d : Category o2}
  (0 f, g : c ->> d) where
  constructor MkNaturalIsomorphism
  nat : f =>> g
  tan : g =>> f
  0 η_φ : (v : o1) ->
    (nat.component v |> tan.component v) {a = (f.mapObj v), b = (g.mapObj v), c = (f.mapObj v)}
       === d.id (f.mapObj v)
  0 φ_η : (v : o1) ->
    (tan.component v |> nat.component v) {a = (g.mapObj v), b = (f.mapObj v), c = (g.mapObj v)}
       === d.id (g.mapObj v)
```



Natural isomorphism are also symetric and transitive.

<!-- idris
public export
-->
````proposition
Natural isomorphisms are symmetric.
```idris
symNT :
  {0 o1, o2 : Type} -> {0 c : Category o1} -> {0 d : Category o2} ->
  {0 f, g : c ->> d} -> f =~= g -> g =~= f
symNT nt = MkNaturalIsomorphism nt.tan nt.nat nt.φ_η nt.η_φ
```
````

````proposition
Natural isomorphisms are transitive.
```idris
public export
transNT :
  {0 o1, o2 : Type} ->
  {0 c : Category o1} -> {d : Category o2} ->
  {f, g, h : c ->> d} ->
  f =~= g -> g =~= h -> f =~= h
transNT nt mt = MkNaturalIsomorphism
  (nt.nat ⨾⨾⨾ mt.nat)
  (mt.tan ⨾⨾⨾ nt.tan)
  -- Proofs in appendix
```
````

```idris {hidden=""}
  (\x => let
    ntc : f.mapObj x ~> g.mapObj x
    ntc = nt.nat.component x
    ntc' : g.mapObj x ~> f.mapObj x
    ntc' = nt.tan.component x
    mtc : g.mapObj x ~> h.mapObj x
    mtc = mt.nat.component x
    mtc' : h.mapObj x ~> g.mapObj x
    mtc'= mt.tan.component x

    0 steps : CongPipeline ? (f.mapObj x ~> f.mapObj x)
    steps =
         -- first we associate to the right
         ((ntc |> mtc) |> (mtc' |> ntc'))
         -- then we're congruent over (ntc|>)
         :: Cong (ntc |>)
                  --then we associate to the left
                 ((mtc |> (mtc' |> ntc'))
                 -- now we're congruent over (|> ntc')
                 :: Cong (|> ntc')
                      -- we apply the rule we have
                      [ mtc |> mtc'
                      , d.id (g.mapObj x)]
                 -- then remove the extra identity on the left
                 >| [ntc']
                 )
        -- finally we apply the other rule
         >| [ntc |> ntc'
            , d.id (f .mapObj x)
            ]
    in runProof steps
        [ sym (d.compAssoc {})
        , d.compAssoc {}
        , mt.η_φ  x
        , d.idLeft {}
        , Refl
        , nt.η_φ x
        ]
  )
  (\x => let
    ntc : f.mapObj x ~> g.mapObj x
    ntc = nt.nat.component x
    ntc' : g.mapObj x ~> f.mapObj x
    ntc' = nt.tan.component x
    mtc : g.mapObj x ~> h.mapObj x
    mtc = mt.nat.component x
    mtc' : h.mapObj x ~> g.mapObj x
    mtc'= mt.tan.component x

    0 steps : CongPipeline ? (h.mapObj x ~> h.mapObj x)
    steps =
      ( ((mtc' |> ntc') |> (ntc |> mtc))
      :: Cong (mtc' |>)
             ( (ntc' |> (ntc |> mtc))
             :: Cong (|> mtc)
                 [ (ntc' |> ntc)
                 , (d.id (g.mapObj x))
                 ]
             >| [mtc]
             )
      >| [d.id (h.mapObj x)])
    in runProof steps
        [ sym (d.compAssoc {})
        , d.compAssoc {}
        , nt.φ_η x
        , d.idLeft {}
        , mt.φ_η x
        ]
  )
```

The above properties ensures natural transformations form a preorder, we make this fact explicit by implementing the relevant interfaces so that we can make use of it later.
````proposition
Natural transformations form a preorder.
```idris
%unbound_implicits on
public export
{a : _} -> Reflexive (a ->> b) (=>>) where
  reflexive = identity

public export
{b : _} -> Transitive (a ->> b) (=>>) where
  transitive f g = f ⨾⨾⨾ g

export
{a, b : _} -> Preorder (a ->> b) (=>>) where
```
````

