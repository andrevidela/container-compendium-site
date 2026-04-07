
## Boundaries

The `Data.Boundary` module holds a single type: `Boundary`.
Its role is to hold two types, in a sense, it's an alias for
`Pair Type Type`. In haskell one could write `type B = (Type, Type)`
for the same definition.


```idris
module Data.Boundary

%default total
```

Why do we need this? It is because boundaries make the representation
of the category of lenses easier to write. It also makes the move
from plain lenses into dependent lenses easier to follow.

```idris
||| Type boundaries
public export
record Boundary where
  constructor MkB
  π1 : Type
  π2 : Type
```

Because it is a record, it is given two projections `π1` and `π2`
so that we can extract each type boundary.

One of the benefits of making it its own type is that we can write
functions like the following just for boundaries:

```idris

public export
cartesian : Boundary -> Boundary -> Boundary
cartesian a b = (MkB (a.π1, b.π1) (a.π2, b.π2))

public export
cocartesian : Boundary -> Boundary -> Boundary
cocartesian a b = MkB (Either a.π1 b.π1) (Either a.π2 b.π2)
```

We also provide a constructor to supply only one type when both
are the same.

And we create a shorthand for the _unit boundary_.

```idris
public export
Dup : Type -> Boundary
Dup ty = MkB ty ty

public export
BUnit : Boundary
BUnit = MkB Unit Unit
```

By themselves, boundaries do not do much, but they are instrumental
in identifying lense as a morphism between two things, those things
are the boundaries we defined here.
