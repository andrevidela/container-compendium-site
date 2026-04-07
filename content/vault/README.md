Container Compendium
--------------------

This repository hosts my work on containers and Monads on containers.

You can use this book as a resource to learn about containers, the reading
order is not linear due to the nature of the code, here are some suggested
entry-points:

- If you want to start from scratch, go to [Start.md](Start.md)
- If you already know about dependent types but not about category theory
  go to [Data.Category](src/Data/Category.idr.md)
- If you already know about category theory and dependent types but want
  to learn about the new stuff, go to [Data.Container.Monad](src/Data/Container/Monad.idr.md)
- If you don't care about the theory but want to learn about the applications
  go to Interactive.Demo
- If you are here because of my thesis, start at [Intro.md](Plan.md)

Here is the dependency tree for how to read this book, because each section
is an Idris module, the tree is automatically generated from the import list.
