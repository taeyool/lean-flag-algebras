\label{sec:results}

Using the formalization infrastructure described in the preceding sections,
we give formally complete proofs of two theorems in extremal combinatorics.
Both proofs are machine-checked in Lean~4 and contain no \lean{sorry}
placeholders in their proof paths.

\subsection{Mantel's Theorem}

Mantel's theorem states that a triangle-free graph on $n$ vertices has at
most $\lfloor n^2/4 \rfloor$ edges, achieved by the complete bipartite graph
$K_{\lfloor n/2\rfloor, \lceil n/2\rceil}$.  In flag algebra terms:

\begin{lstlisting}
theorem Mantel_theorem : K2 ≤ (1/2 : ℝ) • 1 + K3
\end{lstlisting}

Here $K_2$ and $K_3$ are elements of \lean{FlagAlgebra ∅ₜ} representing the
single edge and the triangle.  The inequality asserts that in every sequence
of graphs whose triangle density tends to zero, the edge density is at most
$1/2$.

The proof uses an explicit square in the algebra of 1-vertex-typed flags.
Let $a = \lean{FlagAlgebra\_2\_1\_0\_0}$ and $b = \lean{FlagAlgebra\_2\_1\_0\_1}$
be the two typed flags of size 2 with a 1-vertex type (corresponding to
the two labeled graphs on two vertices with one labeled vertex: one where the
two vertices are adjacent, one where they are not).
Then
\[
  \bigl\llbracket (a - b)^2 \bigr\rrbracket_1
  \;=\;
  2 \cdot K_2 - \mathbf{1}
  \;\geq\; 0
  \;\;\text{in the semantic cone.}
\]
This is enough to conclude $K_2 \leq \frac{1}{2} \cdot \mathbf{1}$ in the
presence of $K_3 = 0$.  The SDP certificate here is small enough to write
explicitly (no external solver needed), making Mantel's theorem a clean
end-to-end illustration of the method before the heavier machinery of the
pentagon proof.

The formal proof in \lean{LeanFlagAlgebras.MantelTheorem.MantelTheorem} uses
\lean{prove\_flag\_expand\_with\_forbidden\_flag} to establish the expansion
identity, \lean{ac\_sort\_pipeline} to normalize the resulting linear
combination, and \lean{flagQuadraticForm\_nonneg} to confirm the semantic
non-negativity.

\subsection{The Erd\H{o}s Pentagon Theorem}

The main result is:
\begin{lstlisting}
theorem ErdosPentagon_Turan
    : generalizedTuranDensity C5 K3 = 24/625
\end{lstlisting}
proved as the conjunction of an upper bound and a lower bound.

\paragraph{Upper bound.}
\begin{lstlisting}
theorem ErdosPentagon_Turan_upperBound
    : generalizedTuranDensity C5 K3 ≤ 24/625 :=
  generalizedTuranDensity_le_of_forbidLE (by norm_num)
    ErdosPentagon_flagAlgebra
\end{lstlisting}
The key lemma \lean{ErdosPentagon\_flagAlgebra} establishes the flag algebra
inequality $C_5 \leq_{[K_3]} \frac{24}{625} \cdot \mathbf{1}$, i.e., that
$C_5$-density is at most $24/625$ under the $K_3$-free assumption.
The proof exhibits three PSD matrices $P, Q, R$ over $\mathbb{Q}$
(one per 1-vertex type, each $8\times 8$) and shows that the sum of the
corresponding quadratic forms, after downward-averaging, equals
$\frac{24}{625} \cdot \mathbf{1} - [C_5]$.

Positive semidefiniteness of each matrix is verified via the LDL$^\top$
approach described in Section~\ref{sec:sdp}.  Once PSD is established, the
quadratic form non-negativity follows from
\lean{flagQuadraticForm\_nonneg}.  The equality between the quadratic form
sum and the claimed bound is verified by the tactic pipeline:
\lean{prove\_flag\_expand\_with\_forbidden\_flag} and
\lean{prove\_flag\_mul\_with\_forbidden\_flag} handle the expansion and
product identities, while \lean{ac\_sort\_pipeline} normalizes the resulting
expressions.

The final one-line proof \lean{ErdosPentagon\_Turan\_upperBound} connects
\lean{ErdosPentagon\_flagAlgebra} to the combinatorial statement via
\lean{generalizedTuranDensity\_le\_of\_forbidLE}.

\paragraph{Lower bound.}
The lower bound
\begin{lstlisting}
theorem ErdosPentagon_Turan_lowerBound
    : generalizedTuranDensity C5 K3 ≥ 24/625
\end{lstlisting}
is proved by an explicit construction.  We define the blow-up of a graph:
\begin{lstlisting}
def blowUp (G : SimpleGraph V) (n : ℕ) : SimpleGraph (V × Fin n) :=
  { Adj := fun v w => G.Adj v.1 w.1 ∧ v ≠ w, ... }
\end{lstlisting}
The $n$-fold blow-up of $C_5$ (replacing each vertex by an independent set
of $n$ vertices and each edge by a complete bipartite graph) is triangle-free:
\begin{lstlisting}
theorem blowUp_K3_free : (blowUp C5 n).CliqueFree 3
\end{lstlisting}
It has $5n$ vertices and at least $n^5$ induced copies of $C_5$:
\begin{lstlisting}
theorem subgraphCount_blowUp_C5_ge (n : ℕ) :
    n^5 ≤ (blowUp C5 n).inducedSubgraphCount C5
\end{lstlisting}
The lower bound on the Turán density follows from the limit:
\[
  \lim_{n\to\infty} \frac{n^5}{\binom{5n}{5}} = \frac{24}{625},
\]
which is proved as an exact algebraic identity using \lean{norm\_num} after
unfolding the definition of $\binom{5n}{5} = \frac{5n(5n-1)(5n-2)(5n-3)(5n-4)}{120}$.
The limit argument is formalized using Lean's \lean{Filter.Tendsto} framework:
\begin{lstlisting}
lemma tendsto_C5_blowUp_density :
    Filter.Tendsto (fun n => n^5 / Nat.choose (5*n) 5)
                   Filter.atTop (nhds (24/625))
\end{lstlisting}

\paragraph{Trust hierarchy.}
The proof of \lean{ErdosPentagon\_Turan} depends on two classes of
computational verification:
\begin{itemize}
  \item \lean{native\_decide} is used for all density table equalities
    (e.g., $\den{F_1,F_2}{G} = p/q$ for specific flags).  This tactic
    compiles the goal to native code and evaluates it; it relies on the
    correctness of the Lean-to-native compiler, which is outside the kernel.
    We accept this trust assumption because each individual density claim is
    a simple rational equality, and the native evaluator has been extensively
    tested in the Lean community.

  \item \lean{decide +kernel} is used for the three SDP matrix equalities
    $P = L_P D_P L_P^\top$, $Q = L_Q D_Q L_Q^\top$, $R = L_R D_R L_R^\top$.
    This tactic evaluates inside the Lean kernel using no compiled native
    code, so it introduces no trust beyond the standard Lean axioms
    (\lean{propext}, \lean{Quot.sound}, \lean{Classical.choice}).
    We use \lean{decide +kernel} specifically here because the SDP
    certificates are the trust-critical component: if a matrix is claimed PSD
    but is not, the entire upper bound proof collapses.
\end{itemize}
In both cases, the external computation (density enumeration scripts
in \lean{LeanFlagAlgebras/ErdosPentagon/Densities/} and the SDP solver in
\lean{LeanFlagAlgebras/ErdosPentagon/Matrix/}) is responsible only for
producing \emph{candidate} values.  The Lean proofs are responsible for
verifying each candidate against the formal definition.  There are no
\lean{sorry}s or \lean{axiom}s in the proof paths of either
\lean{Mantel\_theorem} or \lean{ErdosPentagon\_Turan}.
