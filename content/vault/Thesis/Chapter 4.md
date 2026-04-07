


# Containers as Tactics

The study of containers spans many areas of computer science and type theory. We've already seen how to use them for APIs and design complex software out of smaller building blocks. This section will reuse all the tool and intuition developed until now but apply to a different domain: Theorem proving and tactics.

Theorem provers based on tactics provide a programming environment in which statements are proven given a series of steps that rewrite the initial statement into smaller ones. Those statements are called "goals" and a big part of the interaction model of a tactical theorem prover is based on rewriting the goals until the proof is trivial.

Theorem provers such as Coq/Rock and Isabelle feature tactics as their primary mode of interaction for writing proofs. The latter is particularly interesting since its history involves a core written in ML that verifies statements written using tactics. In that environment. Tactics break down a goal into a list of sub-goals, depending on the nature of the tactic, each sub-goal needs to be solved using other tactics, or maybe only one needs to be. Whatever the case, the solution for the sub-goals is then translated back into a solution for the original goal.

## Containers as Claim, Morphisms as Tactics

The above infrastructure conspicuously looks like a _lens_, what is more, the fact that solutions need to match their original problem statements reinforces the idea that they are _dependent lenses_. The benefits of this observation is that we can now make the abstract notion of "theorem", "goal" and "subgoal" from ML precise.

Here, a goal is a problem statement, a theorem is a proof for that goal, or a _solution_. A sub-goal is merely the forward result of applying a lens to a problem to obtain a different problem.

To make this relation with tactics evident we show how we can use the category of containers ane their morphisms to encode the same structure as the LCF theorem prover. This encoding will already provide better semantics with regards to errors handling and expected return types, I'm addition to the LCF encoding, we provide even stronger types for a tactical system based on equations on natural numbers as well as a natural deduction system.

---

The request/response interpretation of lenses can be taken further to represent pairs of a problem and its solution. This interpretation of lenses dates back to Blass 1993. In that spirit, the Compiler forest uses the term "tactic" to refer to lenses of the form

$(a, a')\Rightarrow(b, b') = \lambda (x : a) . m (\Sigma (y : b). b'(y) \to m(a'(x))$

Where $m$ is a monad in the underlying category.

We recognise this definition from our _enriched dependent lenses_ section used to perform arbitrary effects in the forward part of the lens.

Instead, a tactic for us is a morphism $P \Rightarrow M(P)$ where $P$ is a container representing pairs of problems and their solutions, and $M$ is a monad on containers.
The distinctive feature of a lens as a tactic is that it takes existing problem/solution pairs and breaks them down into smaller problem/solution pairs. The qualities of the morphism itself are not as important as the ability to simplify an input problem into smaller sub-problems, and convert back sub-solutions into an "overall solution" that matches the original problem. This is why we can have tactics using lenses, closed lenses, bidirectional dependent lenses, closed dependent lenses, enriched lenses and enriched dependent lenses.

```tikz {caption="The original problem is broken down into sub-problems and sub-solutions are translated back into a solution for the original problem"}
\usepackage{tikz}
\usepackage{amsfonts}
\begin{document}
\begin{tikzpicture}
\draw (0,0) rectangle (5, 3);
\draw [->] (5,0.5) -- (6, 0.5);
\node [anchor=west] at (6,0.5)  {Sub-solution}; % sub-solution
\draw [<-](5,2.5) -- (6, 2.5);
\node [anchor=west] at (6,2.5)  {Sub-problem}; % sub-problem
\draw [->](-1, 0.5) -- (0, 0.5);
\node [anchor=east] at (-1,0.5)  {Overall solution}; % overall solution
\draw [<-](-1, 2.5) -- (0, 2.5) ;
\node [anchor=east] at (-1,2.5)  {Original problem}; % original problem
\end{tikzpicture}
\end{document}
```

The simplest example of a tactic is an axiom rule: Given a problem statement, we know that it is true without further decomposition of the problem. Such tactic is a lens $PS \Rightarrow I$ where $I$ is the neutral element for the tensor product.

```tikz {caption="An axiom is a problem for which we know an atom-solution."}
\usepackage{tikz}
\usepackage{amsfonts}
\begin{document}
\begin{tikzpicture}
\draw (0,0) rectangle (5, 3);
\draw [<-] (5,0.5) -- (6, 0.5);
\node [anchor=west] at (6,0.5)  {1 (no sub-solutions)}; % sub-solution
\draw [->](5,2.5) -- (6, 2.5);
\node [anchor=west] at (6,2.5)  {1 (no sub-problems)}; % sub-problem
\draw [<-](-1, 0.5) -- (0, 0.5);
\node [anchor=east] at (-1,0.5)  {Solution}; % overall solution
\draw [->](-1, 2.5) -- (0, 2.5) ;
\node [anchor=east] at (-1,2.5)  {Problem}; % original problem
\end{tikzpicture}
\end{document}
```

A tactic that splits a problem in two sub-problems also collects the two sub-solutions and combine them together to build a solution for the original problem. However there are two ways of performing this combination of sub-solutions:

- Either both sub-problems need to be solved.
- Or only one of the two needs to be solved, it doesn't matter which one.

This distinction is known in the types of the lenses that correspond to those tactics. If $PS$ is our problem/solution container, a lens that splits the problem in half but also requires both sub-solutions has type $PS \Rightarrow PS \otimes PS$ . The tensor product ensures the two solutions are present to build a solution to the original problem.

```tikz {caption="A tactic splitting the problem in two and requiring both sub-solutions uses a tensor product in the codomain"}
\usepackage{tikz}
\usepackage{amsfonts}
\begin{document}
\begin{tikzpicture}
\draw (0,0) rectangle (5, 3);
\draw [<-] (5,0.5) -- (6, 0.5);
\node [anchor=west] at (6,0.5)  {sub-solution1 $\times$ sub-solution2}; % sub-solution
\draw [->](5,2.5) -- (6, 2.5);
\node [anchor=west] at (6,2.5)  {sub-problem1 $\times$ sub-problem2}; % sub-problem
\draw [<-](-1, 0.5) -- (0, 0.5);
\node [anchor=east] at (-1,0.5)  {Solution}; % overall solution
\draw [->](-1, 2.5) -- (0, 2.5) ;
\node [anchor=east] at (-1,2.5)  {Problem}; % original problem
\end{tikzpicture}
\end{document}
```
Contrast this with a tactic that only requires one of the sub-solutions to build the overall solution, it would have type $PS \Rightarrow PS * PS$. Using the cartesian product ensures the solutions coming back are bundled in a coproduct

```tikz {caption="A tactic splitting the problem in two and requiring only one of two sub-solutions uses a cartesian product in the codomain"}
\usepackage{tikz}
\usepackage{amsfonts}
\begin{document}
\begin{tikzpicture}
\draw (0,0) rectangle (5, 3);
\draw [<-] (5,0.5) -- (6, 0.5);
\node [anchor=west] at (6,0.5)  {sub-solution1 $+$ sub-solution2}; % sub-solution
\draw [->](5,2.5) -- (6, 2.5);
\node [anchor=west] at (6,2.5)  {sub-problem1 $*$ sub-problem2}; % sub-problem
\draw [<-](-1, 0.5) -- (0, 0.5);
\node [anchor=east] at (-1,0.5)  {Solution}; % overall solution
\draw [->](-1, 2.5) -- (0, 2.5) ;
\node [anchor=east] at (-1,2.5)  {Problem}; % original problem
\end{tikzpicture}
\end{document}
```

---

The simplest example of a tactic is an axiom: Given a problem statement, we know that it is always true without further decomposition into sub-problems. The solution for it is known an unique, an atom, therefore we can return it immediately when presented with such problem. If we are given a container of problem/solutions called $PS$ then an axiom is a lens $PS \Rightarrow I$ where $I$ is the monoidal unit for the tensor product.

Sometimes, a tactic might fail, in that scenario we rely on the $Maybe$ monad on containers. A lens $PS \Rightarrow Maybe(PS)$ is one where the original problem can only sometimes be broken down into a sub-problem.

Using monads we can further generalise our previous notions of sub-problem generation. Using the list monad, we can represent the fact that a lens might generate an arbitrary number of sub-problems, including none. Such a lens has type $PS \Rightarrow List(PS)$, but again there are two types of lists, ones where exactly one sub-problem need to be solved and one where every sub-problem need to be solved. The first one capture lenses of type $PS \Rightarrow PS$ and $PS \Rightarrow PS * PS$ and can be understood as the "there exists" monad on containers. Because of this we write it as $PS \Rightarrow \exists PS$ or $PS \Rightarrow \texttt{Any.List}(PS)$. Similarly, the list monad where _all_ subproblems need to be solved capture lenses like $PS \Rightarrow I$, $PS \Rightarrow PS$ and $PS \Rightarrow PS \otimes PS$. Because we require all subproblems to have a solution, this behave a bit like a "for all" monad on containers, which we denote $PS \Rightarrow \forall PS$ or $PS \Rightarrow \texttt{All.Maybe}(PS)$.

## Types for Inference Rules

Inference rules are commonly used by logicians to describe a logical system. They communicate the rules a system needs to obey to prove statements with it. The syntax of inference rules is _not_ the syntax of the language they describe, because of this, we refer to it as _meta-syntax_ or _meta-language_. That is, it is the language used to describe other languages, we're going to call the described language the _object-language_.

As a meta-language, inference rules are sometimes ambiguous and mix rigorous definitions with prose or annotations outside their basic structure. But this does not need to be the case. Using lenses, we can accurately describe how an inference rule is meant to be read and disambiguate between different common uses.

### The Basics

Let's start with the basics, an inference rule is generally written as

```proof
 B  C
------
   A
```

Where $A$, $B$ and $C$ are syntactic terms in the object-language.

For example, if the object-language is natural deduction we might write:

```proof
A   B
-----
$A∧B$
```

If the language is simply typed lambda calculus we can write

```proof
$Γ \vdash f : a → b$ $Γ \vdash x : a$
-------------------------------------
$Γ \vdash f\ x : b$
```

In general a rule 

```proof
B C 
---
 A
```

is read as "from both $B$ and $C$ we can derive the conclusion $A$". 

Sometimes we write two rules with the same premise to indicate that the conclusion has two possible proofs:

```proof
   A
------- Or-L
$A ∨ B$

   B
------- Or-R
$A ∨ B$
```


This is to be read as "we can prove $A ∨ B$ with either $A$ or $B$".

Usually, inferences rules are laid our right next to each other regardless of the relation with other inference rules so you might see:

```proof
   A
------- Or-Intro-L
$A ∨ B$

   B
------- Or-Intro-R
$A ∨ B$
\\
$A ∧ B$
------- And-Elim-L
   A

$A ∧ B$
------- And-Elim-R
   B
   
A    B
------ And-Intro
$A ∧ B$
```

But this doesn't mean that `And-Elim-L`, `And-Elim-R` and `And-Intro` are related in the same way as `Or-Intro-L` and `Or-Intro-R`.

Sometimes we write an additional condition under which the rule apply. For example.

```proof
$Γ \vdash x : T$ $T \equiv S$
-----------------------------
$Γ \vdash x : S$
```

This condition is not object-language syntax but can be any sort of human prose which greatly expands the expressivity of inference rules.

### The Problem 

Like we just hinted, there is a couple of issues with the meta-syntax of inference rules. For example, when two conclusions are the same, it often means that either rules can be applied, and coming up with a proof means guessing which one of the two will lead to a complete proof.

Some effort has been spent in that regard, for example with andreioli's sequent calculus, they present a difference between _invertible_ and _non-invertible_ rules. Invertible ones are the rules that always apply to a goal, where as non-invertible rules mean that there is a non-deterministic choice to make. 

Another issue is that rules of the form

```proof
A B
---
 C
```

sometimes carry an implicit ordering between $A$ and $B$ where statement $A$ has to be solved _before_ statement $B$, an example of this are the rules for _bidirectional typechecking_ that are meant to be read clockwise starting from the left of the conclusion.

Finally, the ability to attach any prose to a rule, while powerful, also creates an infinite amount of possible ways to create ambiguity and confusion. Despite this added power, such rules do not significantly differ in their appearance to advertise their nature.

### Dependent Lenses for Inference Rules

We can write inference rules as dependent lenses where the object are pairs $(goal, proof)$ and the morphisms are inference rules to a set of sub-problems, and proofs for those sub-problems. 

$(\text{goal}, \text{proof}) \Rightarrow (\text{sub-goal}, \text{sub-proof})$

We write $P$ for the container $(goal, proof)$.

An axiom, written

```proof
-----
  A
```

Is given by the lens $P \Rightarrow I$.

When a rule has two premises, and they are independent, one can see that as a goal generating two independent sub-goals. Therefore the rule

```proof
A     B
-------
$A ∧ B$
```

Can be given by a lens with type $P \Rightarrow P \otimes P$. Where the tensor product makes clear that the two sub-goals are independent from each other.

In the case where $A$ needs to occur _before_ $B$, for example in the rule

```proof

$f \ni a → b$ $x \in a$
-------------------------------------
$f\ x \in b$
```

From the bidirectional simply-typed lambda-calculus. The lens $P \Rightarrow P \rhd P$ tells us that the rule generates two sub-goals but they need to be solved in a specific order. We are going to see a later section an implementation of the bidirectional simply-typed lambda calculus where this is implemented.

Whenever a conclusion has two possible proofs, we have a choice of what sub-goal to solve, but we end up with only one proof. The cartesian product reproduces this behaviour by indicating that, while we create two sub-goals, we only keep one of the, supposedly, the one that results in a complete proof.This is therefore represented by the lens $P \Rightarrow P * P$.

Finally, whenever we add some prose to a rule, what we are doing is adding some arbitrary condition under which the lens might or might now apply. To translate this to a lens, we need to convert the prose into code, and that code needs to be run. If the condition is _true_ then the rule applies, otherwise, it does not. To represent a rule that might or might-not apply, we use the $Maybe$ monad on containers, and such rules are kleisli-morphisms of that monad: $P \Rightarrow Maybe\ P$


## LCF tactics

Lcf tactics were first described in CITE in which we can find the following definition

CODE


The above type signature does not make any claims about the relationship between the claim and its proof `thm`

Rewriting this expression a little bit we can see that it is isomorphic to our definition of plain lenses, and indexing the result of the computation with the input results in our definition of dependent lenses.

This definition suggests that containers represent a query-response pair, where the query, in the theorem proving jargon, is a proposition, and the response is a proof that the proposition holds.

