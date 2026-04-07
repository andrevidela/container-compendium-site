<!-- idris
module Data.Category.Product

import Data.Category
import Data.Category.Functor
import Data.Category.Iso
import public Data.Category.Notation
import Data.Category.Preorder

import Data.Iso
import Data.Iso.Category
import public Data.Product

import Proofs


%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

-- reads as ×
private infixl 5 >:<
-->

## The Categorical Product

```idris
public export
record HasProduct {0 o : Type} (cat : Category o) where
  constructor MkProd

  (>:<) : o -> o -> o
  pi1 : {0 a, b : o} -> a >:< b ~> a
  pi2 : {0 a, b : o} -> a >:< b ~> b
```
```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
&& c
\\
\\
a && {a \times b} && b
\arrow["f"{description}, from=1-3, to=3-1]
\arrow["prod"{description}, from=1-3, to=3-3]
\arrow["g"{description}, from=1-3, to=3-5]
\arrow["{\pi_1}", from=3-3, to=3-1]
\arrow["{\pi_2}", from=3-3, to=3-5]
\end{tikzcd}
\end{document}
```
```idris
  prod : {0 a, b, c: o} ->
         c ~> a ->
         c ~> b ->
         c ~> (a >:< b)
```
```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
&& c
\\
\\
a && {a \times b}
\arrow["f"{description}, from=1-3, to=3-1]
\arrow["prod"{description}, from=1-3, to=3-3]
\arrow["{\pi_1}", from=3-3, to=3-1]
\end{tikzcd}
\end{document}
```
```idris
  0 prodLeft : {0 a, b, c : o} -> (f : c ~> a) -> (g : c ~> b) ->
             (|>) {a=c} {b=(a >:< b)} {c=a}
                  (prod {a} {b} {c} f g)
                  (pi1 {a} {b})
                = f
```
```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
&& c
\\
\\
&& {a \times b} && b
\arrow["prod"{description}, from=1-3, to=3-3]
\arrow["g"{description}, from=1-3, to=3-5]
\arrow["{\pi_2}", from=3-3, to=3-5]
\end{tikzcd}
\end{document}
```
```idris
  0 prodRight : {0 a, b, c : o} -> (f : c ~> a) -> (g : c ~> b) ->
              (|>) {a=c} {b=(a >:< b)} {c=b}
                   (prod {a} {b} {c} f g)
                   (pi2 {a} {b})
                 = g

  0 uniq : {0 a, b, c : o} ->
         (f1 : c ~> a) ->
         (f2 : c ~> b) ->
         (p : c ~> a >:< b) ->
         Start (c -< p >- (a >:< b)
                  -< pi1 {a} {b}>- End a) === f1 ->
         Start (c -< p >- (a >:< b)
                  -< pi2 {a} {b} >- End b) === f2 ->
         prod {a} {b} {c} f1 f2 === p
```

```idris {hidden=""}
public export
(><) : {auto cat : Category o} -> (prod : HasProduct cat) => o -> o -> o
(><) = (>:<) prod

public export
0 (~><~) : (cat : Category o) => (prod : HasProduct cat) =>
        {a, b, c, d : o} ->
        a ~> b -> c ~> d ->
        a >< c ~> b >< d
(~><~) m1 m2 = prod.prod (prod.pi1 {a, b = c} |> m1) (prod.pi2 {a, b = c} |> m2)
```

```idris
record HasCartesianProduct (cat : Category Type) where
```
