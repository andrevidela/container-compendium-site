<!-- idris
module Data.Container.Morphism.Cartesian.Bifunctor

import Data.Container
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Category
import Data.Container.Morphism
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Eq

import Data.Category.Bifunctor

import Data.Iso
import Proofs

import Syntax.PreorderReasoning

-- %hide Relation.Isomorphism.infix.(~=)

%unbound_implicits off

%ambiguity_depth 5

public export
-->

### Sequential Continuation Form a Bifunctor $Cont^{\#} \times Cont \to Cont$


The map on morphisms shows how the first morphism needs to be a cartesian morphism
but the second is a plain dependent lens.

```idris
(~▶~) :
    {0 a, a', b, b' : Container} ->
    (a =#> a') -> (b =%> b') ->
    a ▶ b =%> a' ▶ b'
(~▶~) m1 m2 =
    (exBimap (toLens ? ? m1) m2.fwd)
    (bimapCompBwd m1 m2)

export
contFunctor :
    {0 a, x, y: Container} ->
    (x =%> y) ->
    a ▶ x =%> a ▶ y
contFunctor = (identity a ~▶~)
```

This proof is a bit tricky, we need to define a couple of helpers first.

```idris
bimapCompBwd :
    {0 a, a', b, b' : Container} ->
    (m1 : a =#> a') -> (m2 : b =%> b') ->
    (x : Ex a b.shp) ->
    ((val : a'.pos (m1.fwd x.ex1)) ->
        b'.pos (m2.fwd (x.ex2 ((m1.bwd x.ex1).to val)))) ->
    (val : a.pos x.ex1) ->
    b.pos (x.ex2 val)
bimapCompBwd m1 m2 x y z =
  m2.bwd (x.ex2 z) (replace
      {p = b'.pos . m2.fwd . x.ex2}
      ((m1.bwd x.ex1).toFrom z)
      (y ((m1.bwd x.ex1).from z))
      )

public export 0
bimapCompose :
    {0 a, a', b, b', c, c' : Container} ->
    (f : a =#> b) -> (f' : a' =%> b') ->
    (g : b =#> c) -> (g' : b' =%> c') ->
    (x : Ex a (a' .shp)) ->
    (y : (val : c.pos (g.fwd (f.fwd x.ex1))) ->
        c'.pos (g'.fwd (f'.fwd (x.ex2 ((f.bwd x.ex1).to ((g.bwd (f.fwd x.ex1)).to val)))))) ->
    (z : a .pos x.ex1) ->
    bimapCompBwd (f |▶ g) (f' ⨾ g') x y z ===
    bimapCompBwd f f' x (bimapCompBwd g g' (exBimap (toLens f) f'.fwd x) y) z
bimapCompose
    (MkCartDepLens f1 f2)
    (MkMorphism f1' f2')
    (MkCartDepLens g1 g2)
    (MkMorphism g1' g2')
    (MkEx x1 x2) y z = rewrite (f2 x1).toFrom z in Refl

0
bimapIdentity :
   (a, b : Container) ->
   (vx : Ex a b.shp) ->
   (vy : (val : a.pos vx.ex1) -> b.pos (vx.ex2 val)) ->
   bimapCompBwd (identity a) (identity b) vx vy ≡ vy
bimapIdentity a b (MkEx x1 x2) vy = funExtDep $ \vx => Refl
```

```idris
0 preservesComposition :
    {0 a, a', b, b', c, c' : Container} ->
    (f : a =#> b) -> (f' : a' =%> b') ->
    (g : b =#> c) -> (g' : b' =%> c') ->
    ((f |▶ g) ~▶~ (f' ⨾ g')) ≡
    (f ~▶~ f') ⨾ (g ~▶~ g')
preservesComposition f f' g g' = depLensEqToEq $ MkDepLensEq
    (\x => exEqToEq $ MkExEq (fwdEq f g x)
        (\y => cong (g'.fwd . f'.fwd . x.ex2) (bwdEq f g x y)))
    (\x : Ex a a'.shp =>
     \y : ((val : c.pos (g.fwd (f.fwd x.ex1))) ->
          c'.pos (g'.fwd (f'.fwd (x.ex2 ((f.bwd x.ex1).to ((g.bwd (f.fwd x.ex1)).to val))))))
          => funExtDep $ \z => let
        m1 = (f |▶ g)
        m2 = (f' ⨾ g')
        ks = (((f |▶ g).bwd x.ex1).from z)
        in Calc $
            |~ getbwd ((f |▶ g) ~▶~ (f' ⨾ g')) x y z
            ~= bimapCompBwd (f |▶ g) (f' ⨾ g') x y z
            ~~ bimapCompBwd f f' x (bimapCompBwd g g' (exBimap (toLens f) f'.fwd x) y) z
               ...(bimapCompose f f' g g' x y z)
            ~= (f ~▶~ f').bwd x ((g ~▶~ g').bwd (exBimap (toLens f) f'.fwd x) y) z
            ~= (f ~▶~ f').bwd x ((g ~▶~ g').bwd ((f ~▶~ f').fwd x) y) z
            ~= ((f ~▶~ f').bwd x . (g ~▶~ g').bwd ((f ~▶~ f').fwd x)) y z
            ~= (\z => (f ~▶~ f').bwd z . (g ~▶~ g').bwd ((f ~▶~ f').fwd z)) x y z
            ~= getbwd ((f ~▶~ f') ⨾ (g ~▶~ g')) x y z
    )

public export
ContinuationBifunctor : Bifunctor ContCart Cont Cont
ContinuationBifunctor = MkFunctor
  (uncurry (▶))
  (\x, y, m => m.π1 ~▶~ m.π2)
  (\x => depLensEqToEq $ MkDepLensEq
      (\vx => exEqToEq $ MkExEq Refl (\_ => Refl))
      (\vx, vy => bimapIdentity x.π1 x.π2 vx vy))
  (\a, b, c, f, g => preservesComposition _ _ _ _)
```
