## Conclusion

We've seen two examples of how to implement programming language

The first one attempts one tactic at a time without prior knowledge
of the shape of the problem to solve. The second one exhaustively
matches on all possible problems and picks the right lens to solve
the subproblem found.

Both those approach work but they reveal different strategies for how
to approach theorem proving. In one the first case, we let ourselves
open to adding new tactics easily. Maybe custom ones that are user-defined
or ones that have different performance characteristics, without altering
the existing ones. The tradeoff we are making is that we cannot be sure
we are using all the rules our language has to solve problems, this might be
desirable, for example in the case of a larger language with different
fragments of the language, like a cartesian programming language with a linear
fragment.
In the second case, we gain certainty that we've explored
the entire space of possible tactics to apply, with the ability to diagnose
what tactic failed at what point. The tradeoff is that making changes to
that process is more difficult since we cannot have two tactics solve the
same problem with different performance characteristics without changing
the type of our matching lens. In a sense this tradeoff is reminiscent of
the choice to make between open and closed type families in haskell. Are we
prioritising flexibility, or exhaustiveness?


