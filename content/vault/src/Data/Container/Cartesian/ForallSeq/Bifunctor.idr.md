### `▶` is a bifunctor $\ContCart × \ContCart → \ContCart$

The forall-sequencing product is not a monoidal product on containers,
rather, it is an action of $\Cont^{\#}$ on $\Cont$. To prove this,
we start by proving that it's a bifunctor $\Cont^{\#} × \Cont → \Cont$.
This bifunctor will be the basis for proving the action on containers.


<!-- idris
module Data.Container.Cartesian.ForallSeq.Bifunctor

import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Definition
import Data.Container.Extension
import Data.Container.ForallSeq.Definition
import Data.Container.Morphism

import Data.Category.Bifunctor

import Data.Iso
import Proofs

import Syntax.PreorderReasoning

%unbound_implicits off
-->

First we define the operator `~▶#~` that map morphisms of
$\ContCart × \Cont$ to morphisms in $\Cont$. In other words,
any pairs of a catesian morphism and a dependent lens can be
bundled in a single dependent lens where the boundaries are
the ones of the given morphisms but are applied to `▶`.

Because it is the hardest part of this proof, we start by defining
the map on the backward part of this morphism: `bimapCompbwd`.

- [ ] #thesis/code Undo the comments, find out what doesn't work here

```idris
-- public export
-- bimapCompBwd :
--     {0 a, a', b, b' : Container} ->
--     (m1 : a =#> a') -> (m2 : b =#> b') ->
--     (x : Ex a b.req) ->
--     ((val : a'.res (m1.cfwd x.ex1)) -> b'.res (m2.fwd (x.ex2 ((m1.cbwd x.ex1).to val)))) ->
--     (val : a.res x.ex1) -> b.res (x.ex2 val)
-- bimapCompBwd m1 m2 x y z =
--   m2.bwd (x.ex2 z) (replace
--       {p = b'.res . m2.fwd . x.ex2}
--       ((m1.cbwd x.ex1).toFrom z)
--       (y ((m1.cbwd x.ex1).from z))
--       )
```

While the implementaiton is not particularly tricky, two things are made appearant:
The type is quite large, and the body of the implementation makes use of `replace`.

We've seen previously how `replace` can make proving statements difficult and brittle,
this is one of those cases.

Once the backward map is defined, we can use the same implementation as `○` as a bifunctor
for the forward map to build our map `~▷~`.

```idris
public export
(~▶#~) :
    {0 a, a', b, b' : Container} ->
    (a =#> a') -> (b =#> b') ->
    a ▶ b =#> a' ▶ b'
-- (~▶#~) m1 m2 =
--     (exBimap (toLens a a' m1) m2.fwd) <!
--     (bimapCompBwd m1 m2)
```


The job is only getting started since we now need to prove that this map on morphisms preserves
composition and identities. We start with identity since it is the easiest of the two.

```idris

0 preservesIdentity :
    (0 a, b : Container) ->
    (identity a ~▶#~ identity b) ≡#>≡ identity (a ▶ b)
-- 0 bimapIdentity :
--    (a, b : Container) ->
--    (vx : Ex a b.req) ->
--    (vy : (val : a.res vx.ex1) -> b.res (vx.ex2 val)) ->
--    bimapCompBwd (identity a) (identity b) vx vy ≡ vy
-- bimapIdentity a b (MkEx x1 x2) vy = funExtDep $ \vx => Refl
```

The proof that `▶` preserves composition is rendered difficult due to the use of `replace` in
the implementation of the backward part. This makes equational reasoning break in unexpected places,
with a dreaded error:

> f is not a function

This error occurs when the compiler performs substitutions too eagerly, and find itself replacing
parts of the goal when it should not. Resuling in malformed terms that cannot be applied to their
arguments.

Because of this, one cannot simply use `rewrite` undiscriminately, nor can they use equational reasoning,
only a delicate balance of pattern matching gets the job done.

```idris
%ambiguity_depth 5
-- 0 bimapCompose :
--     {0 a, a', b, b', c, c' : Container} ->
--     (f : a =#> b) -> (f' : a' =#> b') ->
--     (g : b =#> c) -> (g' : b' =#> c') ->
--     (x : Ex a (a' .req)) ->
--     (y : (val : c.res (g.cfwd (f.cfwd x.ex1))) ->
--         c'.res (g'.fwd (f'.fwd (x.ex2 ((f.cbwd x.ex1).to ((g.cbwd (f.cfwd x.ex1)).to val)))))) ->
--     (z : a .res x.ex1) ->
--     bimapCompBwd (f |#> g) (f' ⨾ g') x y z ===
--     bimapCompBwd f f' x (bimapCompBwd g g' (exBimap (toLens _ _ f) f'.fwd x) y) z
-- bimapCompose
--     (MkCartDepLens f1 f2)
--     (f1' <! f2')
--     (MkCartDepLens g1 g2)
--     (g1' <! g2')
--     (MkEx x1 x2) y z = rewrite (f2 x1).toFrom z in Refl
```

Once composition is preserved in the backward part, we can easily inline the proof for
the forward part and give a proof that `~▶#~` preserves composition.

```idris
0 preservesComposition :
    {0 a, a', b, b', c, c' : Container} ->
    (f : a =#> b) -> (f' : a' =#> b') ->
    (g : b =#> c) -> (g' : b' =#> c') ->
    ((f |#> g) ~▶#~ (f' |#> g')) ≡#>≡
    (f ~▶#~ f') |#> (g ~▶#~ g')
-- preservesComposition f f' g g' = depLensEqToEq $ MkDepLensEq
--     (\x => exEqToEq $ MkExEq (cartFwdEq f g x)
--         (\y => cong (g'.fwd . f'.fwd . x.ex2) (cartBwdEq f g x y)))
--     (\x : Ex a a'.req =>
--      \y : ((val : c.res (g.cfwd (f.cfwd x.ex1))) ->
--           c'.res (g'.fwd (f'.fwd (x.ex2 ((f.cbwd x.ex1).to ((g.cbwd (f.cfwd x.ex1)).to val))))))
--           => funExtDep $ \z =>
--            Calc $
--             |~ bwd ((f |#> g) ~▶#~ (f' ⨾ g')) x y z
--             ~= bimapCompBwd (f |#> g) (f' ⨾ g') x y z
--             ~~ bimapCompBwd f f' x (bimapCompBwd g g' (exBimap (toLens _ _ f) f'.fwd x) y) z
--                ...(bimapCompose f f' g g' x y z)
--             ~= (f ~▶#~ f').bwd x ((g ~▶#~ g').bwd (exBimap (toLens _ _ f) f'.fwd x) y) z
--             ~= (f ~▶#~ f').bwd x ((g ~▶#~ g').bwd ((f ~▶#~ f').fwd x) y) z
--             ~= ((f ~▶#~ f').bwd x . (g ~▶#~ g').bwd ((f ~▶#~ f').fwd x)) y z
--             ~= (\z => (f ~▶#~ f').bwd z . (g ~▶#~ g').bwd ((f ~▶#~ f').fwd z)) x y z
--             ~= bwd ((f ~▶#~ f') ⨾ (g ~▶#~ g')) x y z
--     )
```

This proof is quite verbose but the verbosity also allows to read it line by line more easily
The payoff is the relatively simple implementation of bifunctor that follow from the work
above.

```idris
public export
ForallSeqBifunctor : Bifunctor ContCart ContCart ContCart
ForallSeqBifunctor = MkFunctor
  (uncurry (▶))
  (\x, y, m => m.π1 ~▶#~ m.π2)
  (\(a && b) => cartEqToEq $ preservesIdentity a b )
  (\a, b, c, f, g => cartEqToEq $ preservesComposition {})
```
