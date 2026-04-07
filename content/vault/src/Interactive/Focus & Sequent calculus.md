
A focus in sequent calculus tells us how to apply our tactics in a tactical theorem prover to typecheck proofs. By indicating what rules are reversible and what rules aren't we can prioritise the application of reversible rules, constraining the search space to efficiently solve premises that can never fail.

The claim of this chapter is that dependent lenses are tactics and we've shown, by implementing a bidirectional typechecker, and a system for arithmetic equalities, that this is done by translating inference rules into lenses and then composing those lenses together. Focus system give an extra piece of information in our inference rules, the ability to tell what should the next be, because our implementation of tactics as container morphisms gives us very precise types, it is natural to as "what is the type of an invertible rule? And what is the difference between an invertible rule and a non-invertible one?"

## non-invertible rules contain a coproduct in their codomain



## How to optimise typechecking from distributive laws

Given a statement `a =%> b ○ c + b ○ d` we can distribute `b` and solve for it once before moving to the uncertain path: `a =%> b ○ (c + d)`

Those distributive laws tell us how to push the invertible forward as much as possible, ensuring we always typecheck in the fastest way possible.
