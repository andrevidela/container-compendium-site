## Language Ecosystem

Beside the language features, it is useful to remind readers of the features and benefits of the idris ecosystem
that will be used in this work.

### `pack` The package manager

Without a package manager, Idris would not see the number of user libraries it currently has, as
of today, the `pack-collection` counts (TODO: check) packages. Those range from high-performance
array manipulation libraries to implementations of papers or generic serialisation of data
like `TOML` or `Dhall`.

### The NodeJS and Browser backend

Idris was designed with pluggable backends in mind, this design choice bore fruit and we today see
a plurality of backends that generate code from Idris. The two that we are going to use extensively
here are the NodeJS backend, and the browser backend. NodeJS is a well-known runtime for Javascript
application primarily target at implementing server backends. The browser backend is aimed at
compiling javascript code that runs in the browser. Combining those two backends, we can use Idris
to run code both on the client and on the server.

- TODO talk about FFI
- talk about differences e.g. file system, http queries, etc.

### `elab-utils` & `json-simple` Libraries

To manipulate data efficiently across network layers, it is common to rely on a format such as JSON
to serialise and deserialise data between different environement. While writing a library to convert
to and from JSON is not a big challenge, the `json-simple` library already provides this feature and
does it very efficiently. What is more, it synergises with `elab-utils`, a library that leverages
elaborator reflection to derive common interfaces such as `Eq`, `Ord` or `Functor`. In this case,
`elab-utils` is also used to derive `ToJSON` and `FromJSON` instance which allow data types to be
manipulated by `json-simple` directly.

- [ ] show example from codebase using automatic deriving

### `idris2-sqlite` and `idris2-sqlite-node`

`idris2-sqlite` is a library to interact with SQLite3 through a DSL in Idris. Its main appeal is a
domain-specific language for building and running queries in an easy and type-safe way.

- [ ] show example of query built using the DSL

One issue is that the existing version of `idris2-sqlite` is reserved for use with the scheme backends of
idris and is not available on the NodeJS backend. To address this missing piece, i've implemented binding
for NodeJS using `bettersqlite3` as a node dependency in a way that lets us reuse the existing DSL from
`idris2-sqlite`. This way both libraries present the same API even though they use completely different
mechanisms under the hood.

### `PreorderReasoning` Library

The default library to write complex proofs is the `PreorderReasoning` library from `base`. This library
allow to implement a proof by writing out its intermediate steps, as well as the proof that enacts that
step. Once all the steps have been laidout, the library will apply transitivity on each individual step
to obtain a complete proof. There is a generic implementation of this library that allows to use any
type that implements the `Preorder` interface, which we wil use for complex composition of morphisms in
this work.

- [ ] show example of preorder reasoning proof
