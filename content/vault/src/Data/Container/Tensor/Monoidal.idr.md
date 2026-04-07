<!-- idris
module Data.Container.Tensor.Monoidal

import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.Product
import Data.Category.ProductCat
import Data.Category.Monoid
import Data.Category.NaturalTransformation

import Data.Container.Category
import Data.Container.Extension.Definition
import Data.Container.Extension.Properties
import Data.Container.Tensor.Definition
import Data.Container.Tensor.Bifunctor

public export
-->

```idris
unitL : I ⊗ a =%> a
unitL = π2 <! (\_ => (() &&))

public export
unitR : a ⊗ I =%> a
unitR = π1 <! (\_ => (&&()))
```

From this we can build the proof that it is a monoidal product in $\Cont$.
We use the bifunctor just defined `TensorBifunctor`, we call it $F$ in diagrams for brevity.

````proposition
The tensor product forms a monoidal structure in $\Cont$
```idris
public export
TensorMonoidal : Monoidal Cont
TensorMonoidal = MkMonoidal
    TensorBifunctor
    I
    alpha
    leftUnit
    rightUnit
  where
```
````

For the tensor to be monoidal, we need to prove that it is associative. We do this by providing a natural isomorphism between the functors $id×F ; F$ and $F × id ; F$. Due to the nature of programming, we need to add an associator to ensure the functors share the same domain and codomain:

- $f1 : Cont × (Cont × Cont) → Cont = id × F ; F$
- $f2 : Cont × (Cont × Cont) → Cont = \mathit{assocR} ; F × id ; F$

The essence of the natural isomorphism for associativity is captured by the diagram:
```tikz {caption="pentagon diagram for associativity of tensor product"}
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\pentagondiagram{
  node top left={(x, (y, z))},
  node top right={(x, y \otimes z)},
  node mid left={((x, y), z)},
  node bottom left={((x\otimes y), z)},
  node bottom right={x \otimes y \otimes z},
  arrow top={id_x \times F_{y, z}},
  arrow left={assocR},
  arrow right={F_{x,y\otimes z}},
  arrow bottom left={F_{x, y}\times id_z},
  arrow bottom right={F_{x \otimes y, z}}
}
\end{document}
```

The proof itself is routine:

```idris
  alpha : let f1, f2 : (Cont × (Cont × Cont)) ->> Cont
              f1 = ((idF Cont) `pair` TensorBifunctor) ⨾⨾ TensorBifunctor
              f2 = assocR {a = Cont, b = Cont, c = Cont}
                   ⨾⨾ ((TensorBifunctor `pair` idF Cont) ⨾⨾ TensorBifunctor)
          in f1 =~= f2
  alpha = MkNaturalIsomorphism
        (MkNT
            (\v => assocR <! (\x, y => assocL y))
            (\a, b, m => Refl))
        (MkNT
            (\v => assocL <! (\x, y => assocR y))
            (\_,_,_ => Refl))
        (\v => cong2Dep
                 (<!)
                 (funExt $ \(a && (b && c)) => Refl)
                 (funExtDep $ \v => funExt $ \(g1 && (g2 && g3)) => Refl))
        (\v => cong2Dep
                 (<!)
                 (funExt $ \((x1 && x2) && x3) => Refl)
                 (funExtDep $ \v => funExt $ \((x1 && x2) && x3) => Refl))
```

We also need proof that the monoidal unit behaves like a unit on both sides of the bifunctor,
again this is done via a natural isomorphism between the identity functor in $\Cont$ and the
functor $f : \Cont → \Cont  = \mathit{unitL} ; I × id_{\Cont} ; F$

The natural isomorphism for left unit is capuring the information in this diagram:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
x && {(1 , x)} \\ \\
x && {(\mathit{I}, x)}
\arrow["unitL", from=1-1, to=1-3]
\arrow["id"', from=1-1, to=3-1]
\arrow["{I \times id}", from=1-3, to=3-3]
\arrow["F"', from=3-3, to=3-1]
\end{tikzcd}
\end{document}
```

The proof is routine:

```idris
  leftUnit : (Bifunctor.unitL ⨾⨾
             (Const I Cont `pair` idF Cont) ⨾⨾
              TensorBifunctor)
              =~= idF Cont
  leftUnit = MkNaturalIsomorphism
        (MkNT
          (\_ => unitL)
          (\_,_,_ => Refl))
        (MkNT
          (\_ =>
            (MkUnit &&) <! (\_ => π2))
          (\_,_,_ => Refl))
        (\c => cong2Dep
          (<!)
          (funExt $ \(() && a) => Refl)
          (funExtDep $ \x => funExt $ \(() && b) => Refl))
        (\_ => Refl)
```

We do the same for the right unit:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
x && {(x , 1)} \\ \\
x && {(x, \mathit{I})}
\arrow["unitR", from=1-1, to=1-3]
\arrow["id"', from=1-1, to=3-1]
\arrow["{id \times I}", from=1-3, to=3-3]
\arrow["F"', from=3-3, to=3-1]
\end{tikzcd}
\end{document}
```


```idris
  rightUnit : (Bifunctor.unitR ⨾⨾
              (idF Cont `pair` Const I Cont) ⨾⨾
               TensorBifunctor)
               =~= idF Cont
  rightUnit = MkNaturalIsomorphism
      (MkNT
        (\v => unitR)
        (\a, b, m => Refl))
      (MkNT
        (\v => (&& ()) <! (\_ => π1))
        (\_,_,_ => Refl))
      (\v => cong2Dep
        (<!)
        (funExt $ \(x1 && ()) => Refl)
        (funExtDep $ \v => funExt $ \(w && ()) => Refl))
      (\_ => Refl)
```


````proposition
A monoid object with regards to the tensor product forms an applicative functor in $Set$.
```idris
export %hint
ApplicativeFromMonoid :
  (m : MonoidObject {o = Container, cat = Cont} TensorMonoidal) => Applicative (Ex m.obj)
ApplicativeFromMonoid {m }
  = MkApplicative
    (\x => MkEx (m.η.fwd ()) (const x))
    (\(MkEx lf1 lf2), (MkEx lx1 lx2) =>
         MkEx (m.mult.fwd (lf1 && lx1))
           (\z => let ff = m.mult.bwd (lf1 && lx1) z
                  in lf2 ff.π1 (lx2 ff.π2)))
```
````
