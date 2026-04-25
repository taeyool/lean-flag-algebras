\label{sec:intro}

\paragraph{Flag algebras in extremal combinatorics.}
A central question in extremal graph theory is: among all large graphs on $n$
vertices that avoid some fixed graph $H$ as a (not necessarily induced) subgraph, what is the
maximum possible density of copies of another graph $F$?
The \emph{generalized Turán density} $\tdensity{F}{H}$
formalizes this question as a limit:
\[
  \tdensity{F}{H}
    \;=\;
  \lim_{n\to\infty}
  \frac{1}{\binom{n}{|V(F)|}}
  \max\bigl\{\#\text{copies of }F \text{ in } G
             \;\big|\;
             G \text{ is } H\text{-free},\;|V(G)|=n\bigr\}.
\]

Razborov's flag algebra method~\cite{razborov2007flag} provides a
\emph{systematic} framework for deriving upper bounds on such densities.
It works by constructing a graded, commutative $\mathbb{R}$-algebra---the
\emph{flag algebra}---whose elements represent linear combinations of
induced subgraph patterns.  The algebra is equipped with a product encoding
simultaneous occurrence and a semantic ordering: an element $f$ is
\emph{non-negative} (lies in the semantic cone) if its value under every
positive $\mathbb{R}$-algebra homomorphism is $\geq 0$.
Non-negativity certificates for carefully chosen elements yield upper bounds
on Turán densities directly.

In practice, these certificates are produced by semidefinite programming:
one seeks a positive semidefinite matrix $Q$ such that
$f - c\cdot\mathbf{1} = \sum_{i,j} Q_{ij}\cdot e_i e_j$ holds in the algebra
(where the $e_i$ are typed flag basis elements and $c$ is the claimed bound).
An SDP solver finds $Q$ numerically; one must then \emph{verify} that $Q$ is
genuinely positive semidefinite and that the algebraic identity holds exactly.

\paragraph{The formalization challenge.}
Formalizing a flag algebra proof in a proof assistant requires confronting three
distinct, non-reducible categories of proof obligation:

\begin{enumerate}
  \item \textbf{Abstract structure.}  Flags (quotients of labeled graphs under
    isomorphism), the flag algebra (a quotient module equipped with a commutative
    ring structure), positive homomorphisms (the semantic ordering),
    the Turán density (a measure-theoretic limit), and the transfer theorem
    connecting flag algebra inequalities to density bounds.  These are
    conceptually non-trivial but finite in number; each requires careful
    type-theoretic encoding.

  \item \textbf{Data-heavy computation.}  For each pair of flags $(F,G)$
    appearing in the proof, one must certify the exact rational density
    $\den{F}{G}$.  For the Erd\H{o}s pentagon theorem,
    this means hundreds of density values over graphs with up to five vertices
    and flag multiplication tables of similar size.  These values are computed
    externally and must be imported into the proof and verified against the
    formal definitions.

  \item \textbf{Algebraic bookkeeping.}  Flag algebra arguments involve
    manipulating linear combinations of hundreds of flag terms: expanding a
    flag at a larger vertex count, computing products of typed flags, and
    normalizing sums into a canonical form.  Each individual step is routine
    but the aggregate is prohibitively tedious to discharge manually.
\end{enumerate}

These three categories are not merely independent complications; they call for
\emph{qualitatively different} proof techniques.  The abstract structure
requires faithful encoding in a dependent type theory.
The data-heavy computation requires a \emph{reflection} architecture:
a decidably-computable concrete representation whose connection to the abstract
definitions is certified by adequacy theorems, allowing Lean's kernel (or native
evaluator) to check each density value automatically.
The algebraic bookkeeping requires \emph{proof-by-reflection via custom
elaboration tactics} that inspect the syntactic structure of the proof state
and dispatch the right sequence of domain-specific lemmas without manual
guidance.

\paragraph{This paper.}
We present a Lean~4 formalization of Razborov's flag algebra method for
graphs, organized around the two-layer architecture that the challenge analysis
dictates.  The \emph{abstract layer} encodes the mathematical semantics
faithfully in Lean~4's dependent type system, including a novel
\emph{general forbidden-subgraph reasoning rule} that does not require
problem-specific axiomatization.  The \emph{reflection layer} bridges the
abstract definitions to a finitely-computable concrete representation, enabling
automated discharge of density and SDP certificate obligations.

\paragraph{Contributions.}
\begin{itemize}
  \item \textbf{Abstract formalization (\S\ref{sec:abstract}).}
    We formalize the full abstract structure of Razborov's flag algebra in
    Lean~4: flags as quotient types of labeled graphs under isomorphism,
    the flag algebra as a quotient $\mathbb{R}$-module with a commutative ring
    structure, the semantic ordering via positive homomorphisms, and a
    measure-theoretic forbidden-subgraph reasoning framework
    (\lean{forbidLE}, \lean{generalizedTuranDensity\_le\_of\_forbidLE}).
    The forbidden-subgraph rule is formulated inside a \emph{single} ambient
    theory of simple graphs and does not require a per-problem axiom.

  \item \textbf{Reflection architecture (\S\ref{sec:reflection}).}
    We introduce \lean{Sym2Graph}, a finitely-representable graph type with
    decidable equality, and prove adequacy theorems equating abstract flag
    densities to computable \lean{Sym2Graph} densities.  We verify SDP
    certificates via an exact LDL$^\top$ decomposition over $\mathbb{Q}$,
    checked by \lean{decide +kernel}.  We distinguish a deliberate
    \emph{trust hierarchy}: \lean{native\_decide} for density tables (trusts
    the native compiler) and \lean{decide +kernel} for SDP certificates
    (trusts only the kernel).

  \item \textbf{Tactic automation (\S\ref{sec:tactics}).}
    We implement a suite of custom Lean~4 elaboration tactics that exploit a
    canonical naming convention for flag constants as a machine-readable
    encoding: \lean{ac\_sort\_pipeline} for linear normalization (replacing a
    generic sort that times out on expressions with $\sim\!25$ terms),
    and \lean{prove\_flag\_expand\_with\_forbidden\_flag} /
    \lean{prove\_flag\_mul\_with\_forbidden\_flag} for expansion and
    multiplication identities (each collapsing 15--20 manual steps into one
    tactic call).

  \item \textbf{Verified results (\S\ref{sec:results}).}
    We give formally complete proofs of Mantel's theorem and of
    $\tdensity{K_3}{C_5} = 24/625$ (the Erd\H{o}s pentagon theorem), including
    the upper bound via a formally verified SDP certificate and the lower bound
    via an explicit $C_5$-blow-up construction with a formal limit argument.
    To our knowledge, this is the first formalization of the flag algebra method
    in any proof assistant.
\end{itemize}

\paragraph{Paper organization.}
Section~\ref{sec:background} recalls the mathematical background on flag
algebras.  Sections~\ref{sec:abstract}--\ref{sec:tactics} describe the two
formalization layers in detail.  Section~\ref{sec:results} presents the
verified results.  Section~\ref{sec:related} discusses related work, and
Section~\ref{sec:conclusion} concludes.
