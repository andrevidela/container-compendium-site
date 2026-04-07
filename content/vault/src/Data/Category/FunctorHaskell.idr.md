<!-- idris
module Data.Category.FunctorHaskell
-->
### Relation Between the `Functor` Interface and Functors in Category Theory

This is obvious to anyone familiar with functional programming and category theory, but I've seldom seen it written down explicitly so
I've decided to take this time to properly write it down. Some programming languages have a notion of `Functor`
that is chiefly given by the `map` function. `map` has different signatures for different types, for example `map` on lists has the type
`(a -> b) -> List a -> List b`. `map` on `Maybe` has the type `(a -> b) -> Maybe a -> Maybe b`.

If we abstract away the difference and put together what is in common
we obtain something of the shape: `map : (a -> b) -> m a -> m b`,
where `m` stands in for both `List` and `Maybe`. To appropriately write
this as a definition of a programming language, we need to explain what `m` is,
and that will depend on the programming environement. In Idris, `m` is a
function `Type -> Type`, indicating that it takes a `Type` in argument and
returns `Type`. In Haskell, or Scala, `m` is a _higher-kinded type_, that is, a
type that operates on types, the syntax for it in Haskell is `m : * -> *` or
`m: m[_]` in Scala. Once we have some well defined notion for `m` in each
language, we can write a programming interface, in Idris it's an `interface`,
in Haskell a `typeclass` or in Scala a `trait` that will define the common
wrapper around any `map` function, this is the definition of _Functor_ in a
programming language.

```scala
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}
```

```haskell
class Functor f where
    fmap :: (a -> b) -> f a -> f b
```

```{idris module=F}
interface Functor (f : Type -> Type) where
  map : (a -> b) -> f a -> f b
```

We just defined functors as a categorical construct in Idris, so surely there
is an obvious link between what we just did and those different programming
definitions?

Their relation lies in the signature of `f`. In all three definitions above,
`f` always has the same function: to stand in for types with a type parameter.
It was always an operation that manipulates _types_. This means that the
`Functor` interface in those languages is not actually a generic functor
between two categories, but it's _a template for endofunctors_ (functors with the same
source and target) of the category of types. Because we already defined the
category of types and functions (as the category `Set`), and we just defined
`Functor` above, we can define this template as the functor `Functor Set Set`.

Now we can relate our `List` and `Maybe` functors as _values_ of `Functor Set Set`:

```idris
ListF : Functor Set Set
ListF = MkFunctor
    { mapObj = List
    , mapHom = \_, _ => map
    , presId = \a => funExt listMapId
    , presComp = \a, b, c, f, g => funExt (listMapComp f g)
    }
  where
    listMapId : {a : Type} -> (xs : List a) -> map Basics.id xs === xs
    listMapId [] = Refl
    listMapId (x :: xs) = cong (x ::) (listMapId xs)

    listMapComp : {a, b, c : Type} ->
                  (f : a -> b) -> (g : b -> c) -> (xs : List a) ->
                  map (g . f) xs === map g (map f xs)
    listMapComp f g [] = Refl
    listMapComp f g (x :: xs) = cong (g (f x) ::) (listMapComp f g xs)

MaybeF : Functor Set Set
MaybeF = MkFunctor
    { mapObj = Maybe
    , mapHom = \_, _ => map
    , presId = \_ => funExt $ \case Nothing => Refl
                                    (Just x) => Refl
    , presComp = \_, _, _, f, g => funExt $ \case Nothing => Refl
                                                  (Just x) => Refl
    }
```

From this implementation we see two things: Firstly, the map on morphism for
both is given by the function `map : (a -> b) -> List a -> List b` and
`map : (a -> b) -> Maybe a -> Maybe b`, and secondly, using our above definition
requires us to _prove_ that our functor behaves properly, something the
programming languages mentioned above usually do not.

Finally we can confirm that the `map` function is indeed the map on morphism of
endofunctors on `Type` by projecting it out and writing their type explicitly:

```idris
parameters {a, b : Type}

  mapList : (a -> b) -> List a -> List b
  mapList = mapHom ListF a b

  mapMaybe : (a -> b) -> Maybe a -> Maybe b
  mapMaybe = mapHom MaybeF a b
```

<!-- idris
export infix 2 <*!
public export
(<*!) : {0 o1, o2, o3 : Type} -> {0 a : Category o1} -> {0 b : Category o2} -> {0 c : Category o3} ->
      Functor b c -> Functor a b -> Functor a c
(<*!) f g = g ⨾⨾ f
-->
