% [TODO for authors: the global feedback requests reconsidering the paper title.
%  The current title "Formalizing Flag Algebras in Lean 4 via Computational Reflection"
%  is misleading because computational reflection is used only in the verification of
%  SDP certificates and density tables, not in formalizing flag algebra theory itself.
%  Suggested alternatives: "Formalizing Flag Algebras in Lean 4" or
%  "A Lean 4 Formalization of Razborov's Flag Algebra Method".
%  This note is placed here because the title lives in the preamble, outside the
%  Introduction section body.]

\label{sec:intro}

\paragraph{Asymptotic extremal combinatorics and flag algebras.}
A central question in extremal combinatorics is: among all $n$-vertex graphs
that avoid a fixed graph $H$ as a subgraph, how many copies of another graph
$F$ can appear?  Formally, $\mathrm{ex}(n;\,F,H)$ denotes the maximum number
of copies of $F$ in any $H$-free graph on $n$ vertices.  As $n$ grows, this
quantity scales like $\binom{n}{|V(F)|}$, and the limiting ratio
\[
  \pi(F;\,H)
  \;=\;
  \lim_{n\to\infty}
  \frac{\mathrm{ex}(n;\,F,H)}{\binom{n}{|V(F)|}}
\]
is the \emph{Turán density} of $F$ with respect to $H$.
Determining these limits exactly is the central goal of asymptotic extremal
combinatorics.

Razborov's flag algebra method~\cite{razborov2007flag} provides a systematic
algebraic framework for deriving upper bounds on Turán densities: it encodes
density inequalities as a semidefinite programming (SDP) problem, producing
certificates that can be checked mechanically.  Since its introduction, the
method has resolved numerous open problems, including the minimum triangle
density problem~\cite{razborov2008}, the Erd\H{o}s pentagon
problem~\cite{HatamiHKNR13,Grzesik12}, and several Turán-type problems for
graphs and hypergraphs.

\paragraph{The formalization challenge.}
Formalizing a flag algebra proof in a proof assistant requires confronting
two distinct categories of proof obligation that call for qualitatively
different techniques.

\begin{enumerate}
  \item \textbf{Data-heavy computation.}  For each flag algebra argument,
    thousands of flag algebra computations must be certified and imported into
    the proof: subgraph density values between flag pairs and the entries of
    the SDP certificate matrix must all be verified against the formal
    definitions.  Manual verification is infeasible; the proof assistant must
    be made to check these values automatically.

  \item \textbf{Algebraic bookkeeping.}  Flag algebra arguments manipulate
    large linear combinations of flag terms: expanding flags at a larger
    vertex count, computing typed flag products, and normalizing into canonical
    form.  Each step is routine but the aggregate is prohibitively tedious
    to discharge by hand.
\end{enumerate}

The first category calls for a \emph{reflection} architecture: a
finitely-computable concrete representation of graphs and flags whose
correspondence to the abstract definitions is certified by adequacy theorems,
allowing Lean's kernel or native evaluator to check each value automatically.
The second calls for custom elaboration tactics that inspect the syntactic
structure of the proof state and dispatch the appropriate domain-specific
lemmas.

\paragraph{This paper.}
We present a Lean~4 formalization of Razborov's flag algebra method for graphs.
The primary contribution is the formalization of flag algebra theory itself:
flags as quotient types of labeled graphs under isomorphism, the flag algebra
as a quotient $\mathbb{R}$-module with a commutative ring structure, positive
homomorphisms as the semantic ordering, and a general
forbidden-subgraph reasoning framework.
A key departure from Razborov's original axiomatic approach is that forbidden
subgraphs are expressed as a single predicate applied at proof time, operating
inside a single ambient theory of simple graphs and requiring no
per-problem axiomatization.
Built on this abstract layer, a \emph{reflection layer} bridges the abstract
definitions to a finitely-computable concrete representation, enabling
automated discharge of density and SDP certificate obligations.
A \emph{tactic layer} handles algebraic bookkeeping via custom elaboration
tactics.

\paragraph{Contributions.}
\begin{itemize}
  \item \textbf{Flag algebra formalization (\S\ref{sec:abstract}).}
    We formalize the full abstract structure of Razborov's flag algebra in
    Lean~4: flags as quotient types of labeled graphs under isomorphism,
    the flag algebra as a quotient $\mathbb{R}$-module with a commutative ring
    structure, and the semantic ordering via positive homomorphisms.
    A key departure from Razborov's original axiomatic approach is the
    forbidden-subgraph reasoning framework: it is expressed as a single
    predicate applied at proof time, operating inside a single ambient theory
    of simple graphs and requiring no per-problem axiomatization.

  \item \textbf{Reflection architecture (\S\ref{sec:reflection}).}
    We introduce a finitely-representable graph type with decidable equality
    and prove adequacy theorems equating abstract flag densities to computable
    values.  SDP certificates are verified via an exact LDL$^\top$
    decomposition over $\mathbb{Q}$.  We enforce a deliberate \emph{trust
    hierarchy}: density tables are checked by Lean's native evaluator
    (trusting the native compiler), while SDP certificate equalities are
    checked by the kernel alone (trusting only the kernel).

  \item \textbf{Tactic automation (\S\ref{sec:tactics}).}
    We implement custom Lean~4 elaboration tactics for the algebraic
    bookkeeping obligations: a tactic for normalizing linear combinations of
    flag terms (which times out without it on expressions with $\sim\!25$
    terms), and tactics for flag expansion and multiplication identities
    (each collapsing 15--20 manual steps into a single tactic call).
    % [TODO: Making these tactics available as a reusable library for
    %  arbitrary flag algebra arguments is planned as future work.]

  \item \textbf{Verified results (\S\ref{sec:results}).}
    We give formally complete proofs of Mantel's theorem
    ($\pi(K_3;\,K_2) = 1/2$) and of the Erd\H{o}s pentagon theorem
    ($\pi(C_5;\,K_3) = 24/625$), the latter including the upper bound via
    a formally verified SDP certificate.
    To our knowledge, this is the first formalization of the flag algebra
    method in any proof assistant, and in particular the first machine-checked
    proof of the Erd\H{o}s pentagon theorem.
    Mantel's theorem has been formalized before as a standalone result;
    our proof is, to our knowledge, the first to derive it via the flag
    algebra method.
\end{itemize}

\paragraph{Paper organization.}
Section~\ref{sec:background} recalls the mathematical background on flag
algebras.
Section~\ref{sec:abstract} presents the abstract formalization layer:
the type-theoretic encoding of flags, the flag algebra, and the
forbidden-subgraph framework.
Section~\ref{sec:reflection} describes the reflection layer: the concrete
computable graph representation, adequacy theorems, and SDP certificate
verification.
Section~\ref{sec:tactics} covers the tactic layer: the custom elaboration
tactics and their canonical naming convention.
Section~\ref{sec:results} presents the verified results.
Section~\ref{sec:related} discusses related work, and
Section~\ref{sec:conclusion} concludes.
