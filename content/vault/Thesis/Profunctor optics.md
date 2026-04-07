Container morphisms are very close to lenses, and even form a frutiful structure to explain how to build multiple notions of optics from basic building blocks. 

In this context, it's important to recall what existing formalizations of lenses and optics already exist. The two most successful, in my opinion, are vanlaarhoven lenses and profunctor optics. I will spend the next few pages summarizing what makes them so compelling for modeling different kinds of optics. 

## Profunctor optics for general optics 

Optics is the name given to data structures adjacent to lenses. Among those we count prisms, traversals, adapters, and more. Profunctor optics are a family of optics unified under a _profunctorial definition_

A profunctor for a category $C$ is a functor $\mathcal{C}^{op} \to \mathcal{Set}$, such a functor has a map on objects $map_{obj} : | \mathcal{C} | → \mathcal{Set}$ and a map on morphisms $map_{mor} : \forall a, b \in \mathcal{C}. \mathcal