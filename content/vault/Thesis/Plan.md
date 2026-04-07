#  Containers as a programming primitive

This is the start of the thesis, it will inherit all the files from the code I've written
but structure it in a more linear fashion, since those documents are expected to be printed
on paper and links cannot be clicked.

The thesis is structured this way:

- Chapter 0
  - [Special Thanks](Special\ Thanks.md)
  - [[Introduction]]
  - [[Knowledge]]
  - [[Related Work]]
	  - [[HancockSetzer.idr]]
	  - [[Poly.idr]]
    - [[Chapter 1]]
  - [[Research/Container-Compendium/src/Data/Container.idr|Container in Idris]]
  - [[Research/Container-Compendium/src/Data/Container/Category.idr|Categorical structures of containers]]
  - Monoids
  - [[src/Data/Category/Action.idr]]
  - [[Research/Container-Compendium/src/Data/Category/Monad.idr|Monad.idr]]
- Chapter 2, Interactive programs
  - Lenses, Optics, etc
    - [[Research/Container-Compendium/src/Optics/Lens.idr|Plain Lenses]]
    - [[Research/Container-Compendium/src/Data/Container/Morphism.idr|Dependent lenses]]
    - [[Closed.idr|Closed lenses]]
    - [[Research/Container-Compendium/src/Data/Container/Morphism/Linear.idr|Linear Lenses]]

- Chapter 3, Applications to interactive systems
  - [[ErrorLocation.idr|Parsing and error reporting]]
  - [[A DSL for HTTP routing]]
  - [[Containers as request-response mechanisms]]
  - Morphisms as serevers
  - Morphisms as clients
    - Kleenee algebra of clients
  - Server State (Para)
  - Concurrency
- Chapter 4, A tactical system

