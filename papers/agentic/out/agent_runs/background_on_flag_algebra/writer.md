\label{sec:background}

This section recalls the mathematical definitions underlying flag algebras,
following Razborov~\cite{razborov2007flag}, and sets up the notation used
throughout the paper.
For $n \in \mathbb{N}$ we write $[n] = \{1,\ldots,n\}$.
All graphs are finite and simple.

\subsection{Types and Flags}

\paragraph{Types.}
A \emph{type} of size $k$ is a graph $\sigma$ with vertex set $[k]$.
The \emph{empty type} $\emptyset$ (size $k=0$) is the unique graph on the
empty vertex set; flags over $\emptyset$ are just ordinary finite graphs
up to isomorphism.

\paragraph{Flags.}
Fix a type $\sigma$ of size $k$.
A \emph{$\sigma$-flag} is a pair $G^\sigma = (G, \theta)$ where $G$ is a
finite graph and $\theta : [k] \hookrightarrow V(G)$ is an injective map such
that $\sigma$ is isomorphic to $G[\operatorname{Im}(\theta)]$ as a labeled
graph (i.e., $\theta$ is a graph embedding of $\sigma$ into $G$).
The integer $|V(G)|$ is the \emph{size} of $G^\sigma$.

Two $\sigma$-flags $(G_1,\theta_1)$ and $(G_2,\theta_2)$ are
\emph{isomorphic} if there is a graph isomorphism $\phi: V(G_1)\to V(G_2)$
with $\phi \circ \theta_1 = \theta_2$.  The set of isomorphism classes of
$\sigma$-flags of size $n$ is written $\mathcal{F}^\sigma_n$, and
$\mathcal{F}^\sigma = \bigcup_{n \geq k} \mathcal{F}^\sigma_n$.
Each $\mathcal{F}^\sigma_n$ is finite.

\subsection{Subflag Densities}

\paragraph{Single-flag density.}
For $\sigma$-flags $F$ of size $m$ and $G$ of size $n \geq m$, the
\emph{induced density} $\den{F}{G}$ is the probability that a uniformly
random injective map from $V(F) \setminus \operatorname{Im}(\theta_F)$ to
$V(G) \setminus \operatorname{Im}(\theta_G)$ (extending the type embedding)
induces a copy of $F$ in $G$ compatible with the type.  Explicitly:
\[
  \den{F}{G}
  \;=\;
  \frac{\bigl|\{\iota : V(F) \hookrightarrow V(G)
                  \mid \iota \text{ preserves type embedding and induces }F\}\bigr|}
       {\binom{n-k}{m-k}\,(m-k)!}.
\]
This value lies in $[0,1] \cap \mathbb{Q}$ and is invariant under
isomorphism of both $F$ and $G$.

\paragraph{Joint density.}
For $\sigma$-flags $F_1$ of size $m_1$ and $F_2$ of size $m_2$ and a host
flag $G$ of size $n \geq m_1 + m_2 - k$, the \emph{joint density}
$\den{F_1,F_2}{G}$ is the probability that two independently and uniformly
chosen injections from $V(F_i)\setminus [k]$ into $V(G)\setminus [k]$
(sampled without replacement from the same pool) each induce their
respective flag, compatible with the shared type embedding.

\subsection{The Flag Algebra}

Fix a type $\sigma$.  Let $\mathbb{R}[\mathcal{F}^\sigma]$ be the free
$\mathbb{R}$-module with basis $\mathcal{F}^\sigma$.
Define the \emph{zero space} $\mathcal{Z}^\sigma$ as the subspace generated
by all elements of the form
\[
  F - \sum_{G \in \mathcal{F}^\sigma_n} \den{F}{G} \cdot G,
  \qquad F \in \mathcal{F}^\sigma_m,\; n \geq m.
\]
The \emph{flag algebra} is the quotient module
\[
  \mathcal{A}^\sigma \;=\; \mathbb{R}[\mathcal{F}^\sigma] \,/\, \mathcal{Z}^\sigma.
\]
The zero-space relations express the combinatorial identity that, in a
sufficiently large graph, the average density of $F$ over all extensions of
the type embedding equals $\den{F}{G}$.

\paragraph{Multiplication.}
For $[F_1] \in \mathcal{A}^\sigma_{m_1}$ and $[F_2] \in \mathcal{A}^\sigma_{m_2}$,
their product at size $\ell \geq m_1 + m_2 - k$ is
\[
  [F_1] \cdot [F_2]
  \;=\;
  \sum_{G \in \mathcal{F}^\sigma_\ell} \den{F_1,F_2}{G} \cdot [G]
  \;\in\; \mathcal{A}^\sigma_\ell.
\]
This is well-defined on the quotient (independent of $\ell$) and makes
$\mathcal{A}^\sigma$ into a commutative, associative $\mathbb{R}$-algebra
with unit $[\text{type graph } \sigma]$.

\subsection{The Downward Operator and Semantic Non-Negativity}

\paragraph{Downward (unlabeling) operator.}
For a $\sigma$-flag $F$ of size $m$ (type of size $k$), the \emph{downward
operator} $\llbracket F \rrbracket_\sigma$ averages over all ways to embed
the type $\sigma$ into $F$, producing an element of the untyped algebra:
\[
  \llbracket F \rrbracket_\sigma
  \;=\;
  \frac{k!\,(m-k)!}{m!}
  \sum_{\theta: [k]\hookrightarrow V(F)}
  \bigl[(F, \theta)\bigr]_\emptyset,
\]
extended linearly to all of $\mathcal{A}^\sigma$.
The downward operator is an $\mathbb{R}$-module map
$\llbracket\cdot\rrbracket_\sigma : \mathcal{A}^\sigma \to \mathcal{A}^\emptyset$.

\paragraph{Positive homomorphisms.}
A \emph{positive homomorphism} is an $\mathbb{R}$-algebra homomorphism
$\phi: \mathcal{A}^\emptyset \to \mathbb{R}$ satisfying $\phi([G]) \geq 0$
for every graph $G$.
Positive homomorphisms correspond bijectively to convergent graph sequences:
every sequence $(G_n)$ with $|V(G_n)|\to\infty$ such that all flag densities
have limits determines a unique positive homomorphism~\cite{razborov2007flag}.

The \emph{semantic cone} is
$\mathcal{C} = \{f \in \mathcal{A}^\emptyset \mid \phi(f) \geq 0\ \forall \phi\}$.

\begin{theorem}[Razborov~{\cite{razborov2007flag}}]
  \label{thm:sdp-nonneg}
  For any type $\sigma$, flags $e_1,\ldots,e_r \in \mathcal{A}^\sigma$,
  and positive semidefinite matrix $A \in \mathbb{R}^{r\times r}$,
  \[
    \Bigl\llbracket \sum_{i,j=1}^r A_{ij}\, e_i\, e_j \Bigr\rrbracket_\sigma
    \;\in\; \mathcal{C}.
  \]
\end{theorem}

This theorem is the engine behind all SDP-based flag algebra bounds.
Given a target element $f_0 \in \mathcal{A}^\emptyset$ and a claimed bound
$c \in \mathbb{R}$, if one exhibits a PSD matrix $A$ and typed flags $e_i$ such
that
\[
  c \cdot \mathbf{1} - f_0
  \;=\;
  \Bigl\llbracket \sum_{i,j} A_{ij}\, e_i\, e_j \Bigr\rrbracket_\sigma,
\]
then $\phi(f_0) \leq c$ for all positive homomorphisms $\phi$, yielding an
upper bound on the Turán density of the corresponding graph pattern.

\subsection{Turán Densities and the Pentagon Problem}

\paragraph{Generalized Turán density.}
For unlabeled graphs $F$ and $H$, the \emph{generalized Turán density} is
\[
  \tdensity{F}{H}
  \;=\;
  \lim_{n\to\infty}
  \frac{\max\bigl\{|\text{copies of }F\text{ in }G|
                   \mid |V(G)|=n,\; G \text{ is }H\text{-free}\bigr\}}
       {\binom{n}{|V(F)|}}.
\]

\paragraph{The Erd\H{o}s pentagon problem.}
The problem asks for $\tdensity{C_5}{K_3}$: the maximum density of
pentagons in triangle-free graphs.  The answer $24/625$ was proved
independently by Grzesik~\cite{grzesik2012} and by Hatami, Hladk\'y, Kr\'al,
Norine, and Razborov~\cite{hatami2012}.  It is achieved by the blow-up of
$C_5$ (partition $n$ vertices into five nearly-equal groups and add all edges
between consecutive groups in the cycle).  We use this theorem as the main
case study throughout the paper, as it involves all three categories of proof
obligation: abstract structure, data-heavy density computation (hundreds of
rational values over 5-vertex graphs), and heavy algebraic bookkeeping.
