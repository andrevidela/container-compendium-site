### Parameterised Dependent Lenses

Equipped with the tensor product, we can build parameterised dependent lenses using the _para construction_. The para construction only requires
a monoidal product to build the bicategory of parameterised morphisms, because we have that tensor on containers is a monoidal product, we can build the bicategory automatically:

<!-- idris
public export
-->
```idris
ParaDLens : Bicategory Container
ParaDLens = ParaConstr Cont TensorMonoidal
```
