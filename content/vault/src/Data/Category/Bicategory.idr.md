<!-- idris
module Data.Category.Bicategory

import Data.Sigma
import Data.Category
import Data.Category.Monoid
import Data.Category.Bifunctor
import Data.Category.NaturalTransformation

%unbound_implicits off
public export
-->

### Bicategory

The notion of bicategory is one that be conceptualised as "one level higher" than a category.
This happens when we not only need objects and morphisms, but we also need a notion of
morphisms between morphisms, and this extra level of morphisms needs to compose as well.

Therefore, where a category only has objects and morphisms, a bicategory has 0-cells,
1-cells and 2-cells along with morphisms between 2-cells.

| Bicategory | Category |
|------------|----------|
| 0-cells   | objects |
| 1-cells   | morphisms |
| 2-cells   | n/a |
| morphisms | n/a |


2-cells and morphisms are also called _vertical morphisms_ and _horizontal morphisms_
respectively. This is because if we represent morphisms in a 2-d plane we get that
a bicategory is structured this way:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
o1 && o2 && o3
\arrow["m"{name=TL}, bend left, from=1-1, to=1-3]
\arrow["m'"{name=BL, swap}, bend right, from=1-1, to=1-3]
\arrow["n"{name=TR}, bend left, from=1-3, to=1-5]
\arrow["n'"{name=BR, swap}, bend right, from=1-3, to=1-5]
\arrow[Rightarrow, "v", shorten=2, from=TL, to=BL] \arrow[Rightarrow, "v'", shorten=2, from=TR, to=BR]
\end{tikzcd}
\end{document}
```

In this picture, `o1`, `o2`, `o3` are 0-cells, `m` and `m'` are 1-cells between `o1` and `o2`. `v` is a 2-cell between `m` and `m'`.
Similarly `o2` and `o3` have a 1-cells `n` and `n'`, those in turn have a s-cell `v'`. The 2-cells `v` and `v'` have a morphism in between them given by composing them horizontally. This mixture of horizontal composition for arrows between 1-cells hows Hence the names _vertical_ and _horizontal_ morphism.

```idris
record Bicategory (o : Type {- 0-cells -}) where
  constructor MkBiCat

  -- 1-cells
  0 m : o -> o -> Type

  -- vertical morphisms which morphisms are the 2-cells
  vert : (a, b : o) -> Category (m a b)

  -- horizontal morphisms
  horz : (a, b, c : o) -> Bifunctor (vert a b) (vert b c) (vert a c)

%unbound_implicits on

||| A helper to extract 2-cells out of a bicategory
public export 0
two_cell : forall o. (bc : Bicategory o) => {0 a, b : o} -> bc.m a b -> bc.m a b -> Type
two_cell x y = (~:>) (bc.vert a b) x y
```

The above diagram should remind you of something: Functors and natural transformations. Functors map between categories, and natural transformations map between functors horizontally. In fact, categories, functors and natural transformations form a bicategory.

