# Annexe

## How to build monads from actions
Given a monoidal category \defref{def:monoidal-cat} $\cat{C}$ and an Action \defref{def:action} $\oslash : \mathbb{C}× \mathbb{D} → \mathbb{D}$.
As well as a monoid \defref{def:monoid-object} $M \in\mathbb{C}$, we can define the functor $M \oslash \_ : \mathbb{D} → \mathbb{D}$ by partially applying $\oslash$ on $M$

We know that $M \oslash \_$ is a functor because $\oslash$ is a functor already. We need to also prove that it is a monad \defref{def:monad}. To do so, we will provide the 5 components of a monad:

### There is a natural transformation $\mu : M \oslash (M \oslash x) \Rightarrow M\oslash x$

#### The component
We can implement such a natural transformation by providing a component

$\varphi : ∀ x ∈ \mathbb{D}. \mathbb{D}(M\oslash (M\oslash x), M\oslash x)$

Which we can construct  using [[Action#^d12c28|m]] ($m: M \oslash (M \oslash x) \to (M\otimes M) \oslash x$) and [[Monoidal category#^c1f52e|μ]] ($\mu : M \otimes M \to M$). Therefore the complete definition is:

$\varphi = (\mu \times id_x) \circ m_{M, M, x}$

#### The naturality square

We now need to prove that this naturality square commutes:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
x & M\oslash (M \oslash x) & M \oslash x \\\\
y & M\oslash (M \oslash y) & M\oslash y
\ar[from=1-1, to=3-1, "m"]
\ar[from=1-2, to=1-3, "\mu_{x}"]
\ar[from=3-2, to=3-3, "\mu_y"]
\ar[from=1-2, to=3-2, "M\oslash (M\oslash m)"]
\ar[from=1-3, to=3-3, "M\oslash m"]
\end{tikzcd}
\end{document}
```

That is: $∀ x, y ∈ \mathbb{D}. ∀ m∈ \mathbb{D}(x, y). M \oslash m \circ \mu_x = \mu_y \circ M\oslash (M\oslash m)$.

We can prove this by expanding out the definitions of the mapping on morphisms

$M\oslash \_ : \mathbb{D}(x, y) \to \mathbb{D}(M\oslash x, M\oslash y)$
$M\oslash m = id_M \times m$

As well as the definition of $μ_x = (μ \times id_x) \circ a_{M, M, x}$  from which we obtain the square:


```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
M\oslash (M \oslash x) & (M\otimes M) \oslash x) & M \oslash x) \\\\
M\oslash (M \oslash y) & (M\otimes M) \oslash y) & M\oslash y
\ar[from=1-1, to=1-3, "\mu_x", bend left]
\ar[from=1-1, to=1-2, "a_{M,M,x}"]
\ar[from=3-1, to=3-2, "a_{M,M,y}"]
\ar[from=3-1, to=3-3, "\mu_y", bend right]
\ar[from=1-1, to=3-1, "m"]
\ar[from=1-2, to=1-3, "\mu_{x}"]
\ar[from=3-2, to=3-3, "\mu_y"]
\ar[from=1-2, to=3-2, "M\oslash (M\oslash m)"]
\ar[from=1-3, to=3-3, "M\oslash m"]
\end{tikzcd}
\end{document}
```

The top and bottom squares commute by definition of $\mu$, the left square commutes by  [[Action#^d12c28| naturality on a]], and the right square commutes because it can be rewritten as:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
(M\otimes M) \oslash x & M\oslash x \\\\
(M\otimes M) \oslash y & M\oslash y
\ar[from=1-1, to=3-1, "id_{M\otimes M} \times m" swap]
\ar[from=1-2, to=3-2, "id_M \times m"]
\ar[from=1-1, to=1-2, "\mu \times id_x"]
\ar[from=3-1, to=3-2, "\mu \times id_y"]
\end{tikzcd}
\end{document}
```

which commutes since the two squares

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
(M\otimes M) & M \\\\
(M\otimes M) & M
\ar[from=1-1, to=3-1, "id_{M\otimes M} " swap]
\ar[from=1-2, to=3-2, "id_M "]
\ar[from=1-1, to=1-2, "\mu"]
\ar[from=3-1, to=3-2, "\mu"]
\end{tikzcd}
\quad
\begin{tikzcd}
x & x \\\\
y & y
\ar[from=1-1, to=3-1, "m" swap]
\ar[from=1-2, to=3-2, "m"]
\ar[from=1-1, to=1-2, "id_x"]
\ar[from=3-1, to=3-2, "id_y"]
\end{tikzcd}
\end{document}
```

Commute separately, in other words : $m\circ id_x = id_y \circ m$ and $μ \circ id_{M\otimes M} = id_M \circ \mu$, both hold because identity is neutral with respect to composition.

### There is a natural transformation $\eta: Id(x) \Rightarrow M\oslash x$

Here $Id(x)$ is the identity morphism in $\mathbb{D}$.

Because $\oslash$ is an action we already have a [[Action#^f90c73|natural isomorphism]] $e : Id(x) \Rightarrow I \oslash x$ where $I$ is the neutral for the action. By design, our Monoid object is equipped with a morphism $u ∈ D(I, M)$ from which we can derive the natural transformation $e' : I \oslash x \Rightarrow M \oslash x$. Horizontal composition of those two natural transformation gives us the required $e' \circ e : Id(x) \Rightarrow M \oslash x$

### There is a square $\mu_x \circ M\oslash \mu_x = \mu_x \circ \mu_{M\oslash x}$

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{M\oslash (M \oslash (M\oslash x))} & {M \oslash (M \oslash x)} \\\\
{M\oslash (M \oslash x)} & {M\oslash x}
\ar[from=1-1, to=3-1, "\mu_{m\oslash x}"]
\ar[from=1-1, to=1-2, "M\oslash (\mu_{x})"]
\ar[from=3-1, to=3-2, "\mu_x"]
\ar[from=1-2, to=3-2, "\mu_x"]
\end{tikzcd}
\end{document}
```

First we expand the definition of $\mu$  to obtain the diagram:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{M \oslash (M \oslash (M \oslash x))} && {M \oslash ((M \otimes M) \oslash x)} && {M \oslash (M \oslash x)}
\\ {(M \otimes M) \oslash (M \oslash x)} &&&& {(M \otimes M) \oslash x} \\ {M \oslash (M \oslash x)} && {(M \otimes M) \oslash x} && {M \oslash x} \arrow["{id \times a_{M, M x}}", from=1-1, to=1-3] \arrow["{a_{M, M, M \oslash x}}"', from=1-1, to=2-1] \arrow["{* \times id}"', from=2-1, to=3-1] \arrow["{a_{M, M, x}}"{description}, from=3-1, to=3-3] \arrow["{* \times id}"{description}, from=3-3, to=3-5] \arrow["{* \times id}", from=2-5, to=3-5] \arrow["{id \times * \times id}", from=1-3, to=1-5] \arrow["{a_{M, M, x}}", from=1-5, to=2-5]
\end{tikzcd}
\end{document}
```

We then tile the square by adding additional arrows to $M \otimes (M \otimes M) \oslash x$ and $((M \otimes M) \otimes M) \oslash x$

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{M \oslash (M \oslash (M \oslash x))} && {M \oslash ((M \otimes M) \oslash x)} && {M \oslash (M \oslash x)} \\ && {(M \otimes (M \otimes M)) \oslash x} && {(M \otimes M) \oslash x} \\ {(M \otimes M) \oslash (M \oslash x)} && {((M \otimes M) \otimes M)\oslash x} \\ {M \oslash (M \oslash x)} && {(M \otimes M) \oslash x} && {M \oslash x} \arrow["{id \times a_{M, M x}}", from=1-1, to=1-3] \arrow["{a_{M \otimes M, M, x}}"{description}, from=3-1, to=3-3] \arrow["{id \times * \times id}", from=1-3, to=1-5] \arrow["{a_{M, M, M \oslash x}}"', from=1-1, to=3-1] \arrow["{* \times id}"{description}, from=3-1, to=4-1] \arrow["{* \times id}"{description}, from=4-3, to=4-5] \arrow["{a_{M, M, x}}"{description}, from=4-1, to=4-3] \arrow["{a_{M, M\otimes M, x}}", from=1-3, to=2-3] \arrow["{\alpha \times id}", from=2-3, to=3-3] \arrow["{a_{M, M, x}}", from=1-5, to=2-5] \arrow["{* \times id \times id}", from=3-3, to=4-3] \arrow["{id \times * \times id}", from=2-3, to=2-5] \arrow["{* \times id}", from=2-5, to=4-5]
\end{tikzcd}
\end{document}
```

We can prove this by using the [[Monoidal category#^ebab75|pentagon diagram]] for the monoid, the [[Action#^ac9052|Pentagon diagram]] for the action, and the [[Action#^d12c28|naturality of a]]

Here is the naturality square for the square $a1$ instanciated with morphism $id_M \times * \times id_x$
```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{M \oslash ((M \otimes M) \oslash x)} && {M \oslash (M \oslash x)} \\ \\
{(M \otimes (M \otimes M)) \oslash x} && {(M \otimes M) \oslash x} \\
\arrow["{id_M \times (* \times id_x)}", from=1-1, to=1-3]
\arrow["{a_{M, M\otimes M, x}}"', from=1-1, to=3-1]
\arrow["{a_{M, M, x}}", from=1-3, to=3-3]
\arrow["{(id_M \times *) \times id_x}"', from=3-1, to=3-3]
\end{tikzcd}
\end{document}
```

And the naturality square for $a2$ instanciated with the morphism $* \times id_M \times id_x$
```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{(M \otimes M) \oslash (M \oslash x)} && {M \oslash (M \oslash x)} \\ \\
{((M \otimes M) \otimes M) \oslash x} && {(M \otimes M) \oslash x} \\
\arrow["{* \times (id_M \times id_x)}", from=1-1, to=1-3]
\arrow["{a_{M\otimes M, M, x}}"', from=1-1, to=3-1]
\arrow["{a_{M, M, x}}", from=1-3, to=3-3]
\arrow["{(* \times id_M ) \times id_x}"', from=3-1, to=3-3]
\end{tikzcd}
\end{document}
```

### There are two triangles  $\mu \circ \eta_{M\oslash x} = \mu \circ M\oslash \eta _x = id_{M\oslash x}$

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{M \oslash x} && {M \oslash (M \oslash x)} \\ \\
{M \oslash (M \oslash x)} && {M \oslash x}
\arrow[from=1-1, to=3-3, equal]
\arrow["{\eta_{M\oslash x}}", from=1-1, to=1-3]
\arrow["\mu", from=1-3, to=3-3]
\arrow["\mu"', from=3-1, to=3-3]
\arrow["{M\oslash \eta_x}", from=1-1, to=3-1]
\end{tikzcd}
\end{document}
```

Like before, we expand the definition of $\eta$ and $\mu$ to obtain the diagram:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{M\oslash x} && {I \oslash M \oslash x} && {M \oslash M \oslash x} \\ {M \oslash I \oslash x} &&&& {M \otimes M \oslash x} \\ {M \oslash M \oslash x} && {M \otimes M \oslash x} && {M \oslash x} \arrow["{id \times e_x}", from=1-1, to=2-1] \arrow["{id \times u \times id}", from=2-1, to=3-1] \arrow["{e_{M \oslash x}}"', from=1-1, to=1-3] \arrow["{u \times id \times id}"', from=1-3, to=1-5] \arrow["{a_{M, M, x}}", from=3-1, to=3-3] \arrow["{a_{M, M, x}}"', from=1-5, to=2-5] \arrow["{* \times id}", from=3-3, to=3-5] \arrow["{M \oslash M \oslash x}"', from=2-5, to=3-5]
\end{tikzcd}
\end{document}
```

Like before, we are going to tile the square by adding $I \otimes M \oslash x$ and $M \otimes I \oslash x$

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
&&& {M \oslash M \oslash x} \\ && {M \oslash I \oslash x} && {M \otimes M \oslash x} \\ &&& {M \otimes I \oslash x} \\ {M\oslash x} &&&&&& {M \oslash x} \\ &&& {I \otimes M \oslash x} \\ && {I \oslash M \oslash x} && {M \otimes M \oslash x} \\ &&& {M \oslash M \oslash x}
\arrow["{e_{M \oslash x}}"', from=4-1, to=6-3]
\arrow["{id \times e_x}", from=4-1, to=2-3]
\arrow["{u \times id}"'{pos=0.4}, from=6-3, to=7-4]
\arrow["{u \times id \times id}"{pos=0.8}, from=5-4, to=6-5]
\arrow["{a_{M, M, x}}"', from=7-4, to=6-5]
\arrow["{a_{I, M, x}}"', from=6-3, to=5-4]
\arrow["{* \times id}"', from=6-5, to=4-7]
\arrow["{* \times id}", from=2-5, to=4-7]
\arrow["{id \times u \times id}"{pos=0.2}, from=2-3, to=1-4]
\arrow["{a_{M, M, x}}", from=1-4, to=2-5]
\arrow["{a_{M, I, x}}", from=2-3, to=3-4]
\arrow["{id \times u \times id}", from=3-4, to=2-5]
\arrow[from=4-1, to=4-7, equal]
\arrow["{\rho \times id}"{description}, from=4-1, to=3-4]
\arrow["{* \times id}"{description}, from=3-4, to=4-7]
\arrow["{\lambda \times id}"{description}, from=4-1, to=5-4]
\arrow["{* \times id}"{description}, from=5-4, to=4-7]
\end{tikzcd}
\end{document}
```

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{ M\oslash x} &&&&& {M \oslash I \oslash x} && {M \oslash M \oslash x} \\
\\
&& {M\oslash x} && {} & {M\otimes I\oslash x} && {M \otimes M \oslash x} \\
\\ \\
{I\oslash M \oslash x} && {I \otimes M \oslash x} &&& {M\oslash x} \\
\\ {M \oslash M \oslash x} && {M \otimes M \oslash x} &&&&& {M\oslash x}
\arrow["{id \times e_x}", from=1-1, to=1-6]
\arrow[from=1-1, to=3-3, equal]
\arrow["{e_{M \oslash x}}"{description}, from=1-1, to=6-1]
\arrow["{id \times u \times id}", from=1-6, to=1-8]
\arrow["{a_{M, I, x}}"{description}, from=1-6, to=3-6]
\arrow["{a_{M, M, x}}"{description}, from=1-8, to=3-8]
\arrow["{\rho \times id}", from=3-3, to=3-6]
\arrow["{\lambda \times id}"{description}, from=3-3, to=6-3]
\arrow[from=3-3, to=6-6, equal]
\arrow["{id \times u \times id}", from=3-6, to=3-8]
\arrow["{* \times id}"{description}, from=3-6, to=6-6]
\arrow["{* \times id}"{description},from=3-8, to=8-8]
\arrow["{a_{I, M, x}}", from=6-1, to=6-3]
\arrow["{u \times id}"{description}, from=6-1, to=8-1]
\arrow["{* \times id}", from=6-3, to=6-6]
\arrow["{u \times id}"{description}, from=6-3, to=8-3]
\arrow[from=6-6, to=8-8, equal]
\arrow["{a_{M, M, x}}", from=8-1, to=8-3]
\arrow["{* \times id}", from=8-3, to=8-8]
\end{tikzcd}
\end{document}
```

We can prove the central square using the [[Monoidal category#^22ac83|left]] and [[Monoidal category#^f70629|right]] unit laws from the monoidal category. The corner squares commute thanks to the [[Action#^d12c28|naturality of a]] And the remaining four triangles commute thanks to the [[Action#^f90c73^|unit laws]] on the action for the left ones and the [[Monoidal category#^9ae58a|unit laws]] from the monoid $M$ for the right ones.

This way, for any action $\oslash : \mathbb{C}× \mathbb{D} → \mathbb{D}$, we have two monads, one $M \oslash \_$ and one $M \otimes \_$ which is the action of $M$ on itself using its own monoidal operation.
