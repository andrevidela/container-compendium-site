```idris
module Data.Container.Morphism.Parameterised

import Data.Container
import Data.Product
import Data.Coproduct
import Data.Alg
import Data.Category
import Data.Boundary

import Data.Container
import Data.Container.Morphism

import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.State
```

## Parameterised dependent lenses

Lenses, Dependent lenses and many other structures model mapping from one domain to their codomain.
However, this view is a little bit limitting, especially when using those tools to represent impure
computation. An insight provided by (moggi? ref) was that stateful computation can be represented
with a pure function provided it would take the entire computation state in argument and output
a _new_ state.

$f : A → B$
*a pure function*

$f : S × A → S × B$
*a stateful function on state `S`*

To achieve the same effect on lenses we are making use of the _para construction_ on the category
of containers and their morphism:

```idris
||| A dependent parameterised lens defined as the para-construction on dependent lenses
public export
record DPara (l, p, r : Container) where
  constructor MkDPara
  lens : p ⊗ l =%> r
```

I am going to explain later what the para-construction is, since it's a much more general tool
than what we are using it for. But what are we using it for? The above data definition acts as
a type-alias for the type `p ⊗ l =%> r` which is a lens with a tensor product on it domain.
What this achieve is a forward part with type `p.shp * l.shp -> r.shp` which can observe a state
`p.shp` in addition to its input argument, and a backward part with type
`(v : p.shp * l.shp) -> r.pos (fwd v) -> p.pos v.π1 * l.pos v.π2` which returns an indexed
output `l.pos` as expected but also _a state update_ `p.pos`. Such a lens when used with a unit boundary `p \otimes l =%> 1` is isomorphic to
`(v : p.shp * l.shp -> p.pos v.\pi1 * l.pos v.\pi2` which is very much like the state monad mentioned above, except displaying a _dependent state update_ at the end. This is particularly interesting for us since such a dependent type might represent state _diffs_, where only the difference between the old state and the new state is kept, or dependent states, like you would find for the coproduct of lenses.

The para construction on container morphisms results in a rich structure, which we are going to explore now. The first thing to notice is that, much like with lenses and dependent lenses. We can obtain "plain" parameterised lenses by using containers with a constant index as boundaries:

```idris
||| A type-alias for non-dependent parameterised lenses
public export
Para : Boundary -> Boundary -> Boundary -> Type
Para (MkB x s) (MkB p q) (MkB y r) = DPara (x :- s) (p :- q) (y :- r)
```

The composition of parameterised lenses is different than its dependent lens counterpart. We can represent it with the following diagram:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzpicture}

\draw (0.5,0) rectangle (3.5,2);
% left boundary
\draw[->] (-0.5, 1.5) node [left] {$A$} -- (0.5,1.5) ;
\draw[<-] (-0.5, 0.5) node [left] {$\bar{A}$} -- (0.5,0.5) ;
\draw[->] (3.5, 1.5) -- (4.0,1.5) ;
\draw[<-] (3.5, 0.5) -- (4.0,0.5) ;
\draw (5.0,0) rectangle (8.0,2);
% right boundary
\draw[->] (8, 1.5) -- (9,1.5) node [right] {$C$};
\draw[<-] (8, 0.5) -- (9,0.5) node [right] {$\bar{C}$};
\draw[->] (4.5, 1.5) node [left] {$B$}  -- (5.0,1.5) ;
\draw[<-] (4.5, 0.5) node [left] {$\bar{B}$}  -- (5.0,0.5) ;

% parameters right
    \draw [->] (6, 2) -- (6, 2.5) node [above] {$\bar{Q}$} ;
    \draw [<-] (7, 2) -- (7, 2.5) node [above] {$Q$};
% parameters left
    \draw [->] (1.5, 2) -- (1.5, 2.5) node [above] {$\bar{P}$} ;
    \draw [<-] (2.5, 2) -- (2.5, 2.5) node [above] {$P$} ;

% combining parameters
    \draw [->] (3.75, 4.5) -- (3.75, 5.0) node [above, xshift=-2] {$\bar{P} \times \bar{Q}$};
    \draw [<-] (4.75, 4.5) -- (4.75, 5.0) node [above, xshift=2] {$P \times Q$};
% diagonal lines
    % left diagonal
    \draw (1.5, 3) -- (3.75, 4.5) ;
    \draw (6, 3) -- (3.75, 4.5) ;

    % right diagonal
    \draw [<-] (2.5, 3) -- (4.75, 4.5) ;
    \draw [<-] (7, 3) -- (4.75, 4.5) ;

% outer box
    \draw (0, -0.5) rectangle (8.5,4.5);
\end{tikzpicture}
\end{document}
```


```idris

||| Composition of parameterised lenses
public export
(|>) : DPara l p x -> DPara x q r -> DPara l (p ⊗ q) r
(|>) y z = MkDPara $ MkMorphism
  (z.lens.fwd . mapSnd y.lens.fwd . assocL . mapFst swap)
  (\x, w => let
                b = z.lens.bwd (x.π1.π2 && y.lens.fwd (x.π1.π1 && x.π2)) w
                a = y.lens.bwd (x.π1.π1 && x.π2) b.π2
            in (a.π1 && b.π1) && a.π2)
```

On of the primitive operations of parameterised lenses is the ability to forward the parameter and drop the argument. This looks like a "cornering" operation.
```idris
public export
cornerRight : DPara CUnit p p
cornerRight = MkDPara $ MkMorphism π1 (\_, x => x && ())

```

We can also build projection functions analogous to the ones from lenses, except they showcase the parameter as an extra argument.

```idris
public export
(.get) : DPara l p x -> p.shp * l.shp -> x.shp
(.get) y = y.lens.fwd

(.set) : (o : DPara l p r) -> (a : p.shp * l.shp) -> (b : r.pos (o.lens.fwd a)) -> p.pos a.π1 * l.pos a.π2
(.set) y x = y.lens.bwd x
```

What we notice with those projection functions is that we can identify them with a reader and a writer monad

```idris
read : DPara l p x -> l.shp -> Reader p.shp x.shp
read l x = MkReaderT (\y => pure $ l.lens.fwd (y && x))

interface DState (st : Container) (x : Type) where
  constructor MkDState
  runDState : (s : st.shp) -> st.pos s * x

state : (DPara (Const l) (Const p) (Const r)) -> l -> r -> State p l
state l xl xr = ST (\xn => pure $ toPair $ l.lens.bwd (xn && xl) xr )
```

However, due to the dependent nature of our processes, we can only make this transformation with containers with
constant positions. This in itself makes the para-construction compelling: we obtain state-monad semantics but
on dependently-types structures like container morphisms.

Another primitive operation on parameterised lenses is the ability to change the parameter by means of a lens. Again, a graphical intuition helps identifying what is going on here:



```idris
export
reparam : a =%> b -> DPara l b r -> DPara l a r
reparam x y = MkDPara (parallel x (identity {a = l}) |> y.lens)
```

Actually we can take this notion to it's logical conclusion and provide a mapping that maps all three
boundary of our parameterised morphism at once.

```idris
export
comb : l =%> x -> p =%> q -> y =%> r -> DPara x q y -> DPara l p r
comb left top right para = MkDPara $ parallel top left |> para.lens |> right

```
From this we can now redefine `reparam` succintly by providing identity morphisms for the left
and right boundary:

```idris
export
reparam' : a =%> b -> DPara l b r -> DPara l a r
reparam' p = comb identity p identity
```

We can also provide pre-composition and post-composition morphisms the same way:

```idris
export
preCompose : a =%> b -> DPara b p c -> DPara a p c
preCompose p = comb p identity identity

export
postCompose : DPara a p b -> b =%> c -> DPara a p c
postCompose l p = comb identity identity p l
```

Of course another way to see pre-composition and post-composition is by understanding
lenses as parameterised lenses with a unit boundary `DLens' = DPara a CUnit b` and applying
the isomoprhism `CUnit ⊗ p ~ p` after composing a member of `DLens'` with a parameterised
dependent lens.

The next two operations are of a similar nature, the combine dependent lenses and parameterised
lenses in the expected way, and can also be seen as composition with a parametered lens with
a unit parameter. They are most useful in the _server as lenses_ project.

```idris
export
paraLeft : a =%> b -> DPara l p r -> DPara (a ⊗ l) p (b ⊗ r)
paraLeft x y = MkDPara (MkMorphism (assocL . mapFst swap . assocR)
                          (\_ => assocL . mapFst swap . assocR) |> parallel x y.lens)

export
paraRight : DPara l p r -> a =%> b -> DPara (l ⊗ a) p (r ⊗ b)
paraRight x y = MkDPara (MkMorphism assocR (\_ => assocL) |> parallel x.lens y)
```

The general parallel composition of lenses can be written as follows:

```idris
public export
parallel : DPara l p r -> DPara x q y -> DPara (l ⊗ x) (p ⊗ q) (r ⊗ y)
parallel p1 p2 = MkDPara $ let p = parallel p1.lens p2.lens in MkMorphism shuffle (\((a && a') && (c && c')) => shuffle) |> p
```

Finally, just like container morphisms, parameterised dependent lenses also have an external
choice operator that takes the coproduct of all boundaries.

```idris
public export
choice : DPara l p r -> DPara x q y -> DPara (l + x) (p * q) (r + y)
choice z w = MkDPara $ MkMorphism fwd bwd
  where
    fwd : (p.shp * q.shp) * (l.shp + x.shp) -> r.shp + y.shp
    fwd (x && (<+ v)) = <+ z.lens.fwd (x.π1 && v)
    fwd (x && (+> v)) = +> w.lens.fwd (x.π2 && v)

    bwd : (arg : (p .shp * q .shp) * (l .shp + x .shp)) -> choice r.pos y.pos (fwd arg) ->
          (p.pos arg.π1.π1 + q.pos arg.π1.π2) * choice l.pos x.pos arg.π2
    bwd (p1 && (<+ v)) x = let val : p .pos (p1 .π1) * l.pos v
                               val = z.lens.bwd (p1.π1 && v) x
                            in <+ val.π1 && val.π2
    bwd (p1 && (+> v)) y = let val : q.pos p1.π2 * x.pos v
                               val = w.lens.bwd (p1.π2 && v) y
                            in +> val.π1 && val.π2
```

### Para construction recap

To quickly recap the para construction. Given a category $\mathbb{C}$ with morphisms $\mathbb{C}(a, b)$
and a monoidal structure on its objects $(|\mathbb{C}|, ⊗, 1)$ we obtain the para-construction by
replacing each morphism $a → b$ by $Σ p : |\mathbb{C}| . p ⊗ a → b$. Depending on your point of view, this
is either a Category with the objects and morphisms given above. Or a _Bicategory_ with reparametrisations
as  vertical morphisms and composition as horizontal morphisms. Of course, Bicategories are also 2-categories
with strict equalities, so you might want to see them that way if that is a more useful tool for your
presentation. Personally I found the bicategorical representation quite neat to implement and so I will
stick with that.
```idris

idPrfLeft : (f : a =%> b) -> f |> Morphism.identity {a=b} = f
idPrfLeft {f = (MkMorphism get set)} = Refl

idPrfRight : (f : a =%> b) -> Morphism.identity {a} |> f = f
idPrfRight {f = (MkMorphism get set)} = Refl

parameters {l, r : Container}
  Repar : (p ** DPara l p r) -> (p ** DPara l p r) -> Type
  Repar x y = x.fst =%> y.fst

  comp : {a, b, c : (p ** DPara l p r)} -> Repar a b -> Repar b c -> Repar a c
  comp = (|>)

  prfAssoc2 : {a, b, c, d : (p ** DPara l p r)}  ->
              (f : Repar a b) -> (g : Repar b c) -> (h : Repar c d) ->
              (comp {a} {b} {c=d} f (comp {a=b} {b=c} {c=d} g h)) === (comp {a} {b=c} {c=d} (comp {a} {b} {c} f g) h)
  prfAssoc2 (MkMorphism fget fset) (MkMorphism gget gset) (MkMorphism hget hset) = Refl

  DParaCat : Category (p ** DPara l p r)
  DParaCat = MkCategory
    Repar
    (\_ => identity)
    (|>)
    idPrfLeft
    idPrfRight
    prfAssoc2

-- Move those two away, probably somewhere close to `Action`?
interface Semigroup a => Combine a (0 b : a -> Type) where
   combine : (x1, x2 : a) ->
             (y : b (x1 <+> x2)) ->
             b x1 * b x2

||| Precomposing a choice with the `x + x = 2 * x` isomorphism
chooseBool : DPara ((!>) l s) p r ->
             DPara ((!>) l s) q y ->
             DPara ((!>) (l * Bool) (s . π1)) (p * q) (r + y)
chooseBool l1 l2 = MkMorphism (\x => if x.π2 then <+ x.π1 else +> x.π1)
                              (\case (x && True) => id
                                     (x && False) => id) `preCompose` (l1 `choice` l2)

```

```idris



```
A `Readonly` container makes the state unmodifiable by bidirectional processes.

```idris
public export
ReadOnly : Container -> Container
ReadOnly (a !> b) = a :- ()
```

This is because a query `Readonly p ⊗ x =%> CUnit` is isomorphic to `(v : (Readonly p ⊗ x).shp) -> (Readonly p ⊗ x).pos v`
which, once expanded is `(v : p.shp * x.shp) -> const () v.π1 * x.pos v.π2` which again is the same as
`p.shp -> (v : x.shp) -> x.pos v`. That is, we can observe the state `p.shp` but we cannot provide an udpate for it.
Therefore, any lens with a `ReadOnly` state is guaranteed to never modify it. This makes parameterised readonly lenses
akin to a reader monad on state.
