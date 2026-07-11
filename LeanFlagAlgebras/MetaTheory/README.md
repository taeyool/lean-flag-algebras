# MetaTheory — a Lean 4 formalisation of the root-plantability meta-theory of flag algebras

This directory formalises, in Lean 4 (toolchain `leanprover/lean4:v4.27.0`, Mathlib `v4.27.0`),
the **proved results of Sections 1–10 of [`paper.tex`](./paper.tex), together with the §11.2–§11.8
relative (slice) theory** — the *meta-theory* of flag algebras that asks **when forbidden-subgraph
("quotient") reasoning is complete** for a constrained graph class, when it can fail, and how a
further constraint sharpens it. The §11.4–§11.8 layer carries the paper's **slice method**
end-to-end — the relative planted set and the relative Positivstellensatz, the Turán/Mantel and
`K₄`-free-`P₄` equality slices mined through a verified certificate, and a self-contained
**graphon layer** delivering the kernel-level moment identities, rigidity, and quantitative
stability.

The headline result is:

> **`clone_root_plantable`** ([`CloneClosed.lean`](./CloneClosed.lean)) — every clone-closed
> hereditary graph class is *root-plantable*: for a non-degenerate type `σ`, the supported space
> `S_σ` equals the quotient space `Q_σ`. Consequently quotient semantics and ensemble semantics
> agree for **every** `f ∈ A^σ`. Specialised to `K_r`-free graphs, this is **`cor:clique-free`**
> (`clique_free_root_plantable` / `clique_free_quotient_iff_ensemble`), covering the
> triangle-free case `r = 3`.

The same conclusion holds for classes closed under **complete blow-ups** (true twins, §6),
**substitution** (§7), and cluster graphs — and §5, §6 and §7 are in fact **one theorem**:

> **`blowupClosed_root_plantable`** ([`BlowupClosed.lean`](./BlowupClosed.lean), paper
> `thm:blowup-root-plantable`) — every **blow-up-closed** hereditary class is root-plantable.
> A class is *blow-up-closed* if one may always blow up a single vertex of a member to an
> arbitrarily large graph, *choosing* the interior, without leaving the class (`BlowupClosed`).

Clone-closed (§5, `clone_root_plantable_blowup`), true-clone-closed (§6, `true_clone_root_plantable`,
with `cluster_root_plantable`), and substitution-closed (§7, `substitution_root_plantable`) are each
a one-line corollary, via the corresponding `…toBlowupClosed` implication. Blow-up-closure is the
*existential* ("some interior works") weakening of substitution-closure's *universal* ("every
interior works") — strictly weaker, so unlike substitution-closure it covers §5 and §6 as well.

**§8 goes beyond global closure**, with a *finite, local* root-plantability criterion and its first
non-closure application:

> **`finitePlanting_root_plantable`** ([`FinitePlanting.lean`](./FinitePlanting.lean), paper
> `thm:finite-local-planting`) — if a hereditary class has the **finite planting property** at a
> non-degenerate `σ` (every large in-class `σ`-flag can be replaced by a larger in-class graph with
> a positive-density set of `σ`-embeddings whose bounded-size flag densities match), then it is
> root-plantable. This is the §5/§7 capstone argument with the blow-up sequence replaced by an
> *abstract* planting family — so the dense, **not blow-up-closed** `C₅`-free class qualifies via a
> sparse local repair (`sparseRootRepair_finitePlanting`), giving `c5free_one_root_plantable`
> (`S₁ = Q₁`) and `c5free_two_root_nonedge_plantable` (`S_η = Q_η`).

**All of §9 (obstructions) is formalised** — §9.1–§9.5, the "negative" side, where quotient
reasoning is *strictly stronger* than ensemble reasoning:

> **`pinning_obstruction`** ([`Pinning.lean`](./Pinning.lean), paper `thm:pinning`) — if a
> labelled quantity is almost surely pinned to one value under every admissible random extension,
> but some quotient point takes a different value, then `S_σ ≠ Q_σ`.  Its concrete instances are the
> **degeneracy obstruction** `degenerate_not_rootPlantable` (`thm:degenerate-obstruction`) and the
> dual **dense obstruction** `coDegenerate_not_rootPlantable` (`cor:codegenerate`): the one-root edge
> density is boundary-pinned to `0` (resp. `1`) across all constrained limits, while a star (resp.
> co-star) realises the opposite boundary in `Q_vtype`.  The `C₄`-free class
> (`c4free_not_rootPlantable`, `lem:c4-edge-zero`) and its dense complement
> (`coC4free_not_rootPlantable`) are explicit such classes.

> **`no_interior_pinning`** ([`NoInteriorThinning.lean`](./NoInteriorThinning.lean), paper §9.4
> `thm:no-interior`, `subsec:boundary`) — for an **edge-deletion-closed** class, a `σ`-flag pinned to
> a constant `c` on the boundary support space `S_σ` necessarily has `c ∈ {0,1}`: pinning can only
> happen at the *boundary*, never in the interior. The proof is the edge-thinning stack — a random
> Bernoulli thinning of in-class graphs whose flag moments converge, as `λ → 0`, to a `{0,1}`-valued
> "edgeless cloud" profile that an L¹/Markov cylinder argument places into `S_σ`.

> **`c5free_edge_not_rootPlantable`** ([`C5EdgeObstruction.lean`](./C5EdgeObstruction.lean), paper
> §9.5 `thm:c5-edge-not-root-plantable`, `sec:c5-edge`) — the `C₅`-free class is **not**
> root-plantable at the two-root **edge** type, refuting the natural "root-plantable at *every* type"
> conjecture (it *is* root-plantable at the one-vertex and two-root non-edge types, §8). The
> common-neighbour triangle flag `F_△` is a.s. pinned to `0` under random edge-rooting
> (`ae_Ftri_eq_zero_of_pinned`, `cor:c5-edge-pinned`) — driven by `lem:c5-few-triangles`
> (`c5free_three_mul_triangle_le`, `3·T(G) ≤ 2·e(G)`) — yet the `C₅`-free **book graph**
> (`bookLabeled`, `def:c5-book`) is `C₅`-free (`book_c5free`) with `F_△`-density `1`, giving a
> `Q_τ` quotient point at the opposite value.

**`lem:complementation` (Lemma 50) — root-plantability is invariant under graph complementation — is
also formalised** (`complementation_invariance`, the four-module `FlagComplement` / `ComplementHom` /
`ComplementClass` / `ComplementInvariance` stack), via the complement *homeomorphism* of
homomorphism spaces rather than the paper's explicit flag-algebra complement isomorphism (a
documented proof-route deviation, Deviation 9b). The only §9 result that remains future work is the
general pinning **conjecture** `conj:characterisation` — see [Scope & limitations](#scope--limitations).

**§10 shows the obstructions are harmless for actual density bounds:**

> **`no_closed_certificate_gap`** ([`CertificateCones.lean`](./CertificateCones.lean), paper §10
> `thm:no-closed-certificate-gap`) — for **every** type, the sums-of-squares certificate cone and
> the "non-negative on `S_σ`" ensemble cone have the *same* `Q₀`-seminorm closure. Together with the
> empty-type collapse `emptyType_rootPlantable` (`prop:empty-type`: `Ext_∅(φ₀) = δ_{φ₀}`, so
> `S_∅ = Q₀`, always root-plantable) and the single-point collapse of the §9 counterexamples
> (`prop:single-point`), this says the quotient/ensemble gap is **invisible to any empty-type density
> bound** — the whole obstruction half of the paper costs nothing in applications
> (`DownwardAverage` / `EmptyTypeCollapse` / `CertificateCones` / `VanishingIdeal` / `BooleanPoint` /
> `SinglePoint` / `C5EdgeInert`).

**§11.2–§11.3 relativises the theory to an arbitrary constraint set** `Y` of admissible limits — the
foundation of the paper's *slice method*:

> **`relative_slackness_*`** and **`kernel_slackness_*`** ([`RelativeSlackness.lean`](./RelativeSlackness.lean),
> [`KernelSlackness.lean`](./KernelSlackness.lean), paper `thm:relative-slackness` /
> `thm:kernel-slackness`) — over the relative support `S_σ(Y)` (`relSσ`, `RelativeSupport`; the
> unconditional criterion `relative_criterion`, closure-invariance `relSσ_closure_eq`), an SOS/PSD
> certificate yields soundness, `√Δ`-rate control of every first moment (`cor:sos-first-moments`),
> and — on the equality slice — the exact vanishing of every certificate term (the labelled moment
> vector falls into `ker Q`). This is the machinery the applied §11.4–§11.8 slice results
> (Turán/Mantel slices, the `K₄`-free-`P₄` equality slice) are built on — and those applied
> instances are now formalised too:

**§11.4–§11.8 is the slice method in action**, from the abstract completeness theory down to a
concrete extremal problem and its stability:

> **`relative_positivstellensatz`** ([`RelativePositivstellensatz.lean`](./RelativePositivstellensatz.lean),
> paper `thm:relative-positivstellensatz`) — every density bound valid on an equality slice is
> provable, up to an arbitrarily small `ε·1₀` shift of the constant, on the **whole** class plus a
> finite quadratic penalty `M·∑ gⱼ²` (compactness of `Q₀`). Together with the relative planted set
> `Q_σ(Y)` and its structure theory (`relQσ` / `RelativelyRootPlantable`,
> `prop:relative-plantability`, [`RelativePlanted`](./RelativePlanted.lean)), the slice
> no-closed-gap theorem (`no_relative_closed_certificate_gap`,
> [`RelativeCertificateGap`](./RelativeCertificateGap.lean)), and the Mantel-slice failure of
> *relative* root-plantability (`mantel_not_relatively_plantable`,
> [`MantelNotPlantable`](./MantelNotPlantable.lean)), this settles §11.4.

> **`equality_slice_vanishing` → `parametricP4_*`**
> ([`CertificateSliceVanishing.lean`](./CertificateSliceVanishing.lean),
> [`ParametricP4Slice.lean`](./ParametricP4Slice.lean); paper `prop:equality-slice-vanishing`,
> `thm:k4free-p4-equality-slice`, `thm:parametric-p4-equality-slice`) — the verified parametric
> certificate `CompleteGraphFreeP4.gap_identity` from the repository's `Automation` layer is fed
> through the relative-slackness machinery, mining the labelled `η`/`τ` slice equations and the
> extremal `K₄` density on the `P₄` equality slices (unconditionally at `r = 3`; via the `hZykov`
> hypothesis for general `r`). The Turán/Mantel slices are nonempty via the Turán-graph limit
> ([`TuranLimit`](./TuranLimit.lean)), and the recovery / qualitative-stability corollaries follow
> in [`SliceRecovery`](./SliceRecovery.lean) — classical equality cases entering as named
> hypotheses (Deviation 14a).

> **`turan_slice_identity_*`** ([`TuranSliceIdentities.lean`](./TuranSliceIdentities.lean), paper
> `thm:turan-slice` / `thm:relative-mantel`, the identity halves) — under the single named
> Erdős–Simonovits hypothesis `hES`, the relative supports of the Turán slice are **single points**
> with the paper's explicit rooted densities (`e = (r-1)/r`; `a_τ = b_τ = 1/r`, `g_τ = (r-2)/r`,
> `z_τ = 0`; `z_η = 1/r`, `g_η = (r-1)/r`, `a_η = b_η = 0`). The route is **not** the paper's
> graphon computation: Turán graphs are vertex- and ordered-pair transitive
> ([`TuranAut`](./TuranAut.lean)), so every finite rooting measure is *exactly* Dirac and
> Dirac-ness passes to the weak limit ([`TuranDirac`](./TuranDirac.lean); Deviation 15). This
> discharges `MantelNotPlantable`'s pinning hypothesis
> (`mantel_not_relatively_plantable_of_uniqueness`) and completes Cor 105's "consequently"
> support identities (`parametric_recovery_identities`).

> **`Graphon.slice_rigidity`** ([`GraphonRigidity.lean`](./GraphonRigidity.lean), paper
> `thm:slice-rigidity`) — a self-contained **graphon layer** ([`GraphonBasic`](./GraphonBasic.lean);
> Mathlib has no graphons) proves the kernel-level §11.7–§11.8 results: the exact and approximate
> moment identities ([`GraphonMoments`](./GraphonMoments.lean), `thm:parametric-moments` /
> `thm:approximate-moments`); rigidity at the regular endpoint — any graphon satisfying the two
> mined local equations at edge density `(r-1)/r` **is** the balanced complete `r`-partite graphon
> (in measurable-partition form, Deviation 14c), unconditionally at `r = 3` (`r3_rigidity`,
> `cor:r3-rigidity`); and quantitative stability
> ([`GraphonQuantStability`](./GraphonQuantStability.lean), `thm:k4free-p4-quant-stability` /
> `thm:parametric-quant-stability`).

> **`graphonHom`** ([`GraphonHom.lean`](./GraphonHom.lean); no single `paper.tex` display — the
> §11.7 area treats "every graphon is a limit object" as folklore input) — **every graphon is a
> positive homomorphism**. For a graphon `W`, the induced flag density
> ([`GraphonInducedDensity.lean`](./GraphonInducedDensity.lean)) `graphonFlagDensity W G` (the
> probability that a `W`-random graph on `|G|` samples equals `G` exactly, with relabelling
> invariance, an extension partition, and a block-product identity) assembles into a profile
> `graphonProfile W : FlagDensitySpace ∅ₜ` satisfying the three homomorphism laws —
> normalisation, the chain rule, and multiplicativity
> (`graphonProfile_oneProp`/`_zeroSpaceProp`/`_mulProp`) — via
> `positiveHomFromZeroSpaceOneMulProp`, giving `graphonHom W : PositiveHom ∅ₜ`. The chain rule and
> multiplicativity are both proved by a **subset-averaging** argument over the new bridge modules
> [`PairSubsetCount.lean`](./PairSubsetCount.lean) and
> [`EmptyTypeGraphBridge.lean`](./EmptyTypeGraphBridge.lean) (`flagDensity₁_graphFlag`/
> `flagDensity₂_graphFlag`, `exists_perm_comp_emb(_pair)`) — no automorphism/orbit-stabiliser
> counting is needed (Deviation 16). The sanity link
> `graphonHom_edge : φ_W(unlabelledEdgeFlag) = W.edgeDensity` ties this new flag-algebra-side
> construction back to the §11.7 kernel layer. This is the **graphon→hom** half of the (still only
> partly formalised) Lovász–Szegedy representation bridge — infrastructure toward
> `thm:k4free-p4-tripartite` / `cor:top-endpoint-recovery`; the harder, remaining half (every
> homomorphism is represented by some graphon) is future work.

**The rooted transport** ([`HOM_TO_GRAPHON_DESIGN.md`](./HOM_TO_GRAPHON_DESIGN.md)) carries `φ_W`
all the way to the kernel hypotheses of `r3_rigidity`:

> **`k4freeP4_graphon_tripartite`** ([`GraphonKernelTransport.lean`](./GraphonKernelTransport.lean))
> — any graphon `W` whose `φ_W` lies in the `K₄`-free `P₄`-slice (with both root types of positive
> mass) is almost everywhere the balanced complete tripartite graphon. This is **the graphon-side
> content of `thm:k4free-p4-tripartite` (Thm 102)**: composing with the still-open hom→graphon
> direction of the Lovász–Szegedy representation theorem (`hrep`) yields the paper statement
> verbatim. The route is a five-module rooted
> stack — [`StdRootedBridge`](./StdRootedBridge.lean) (standard-rooted graphs and the root-fixing
> permutation engine), [`GraphonRootedDensity`](./GraphonRootedDensity.lean) (the pinned-root
> induced density `unnormRootedDensity` and its calculus), [`GraphonRootedHom`](./GraphonRootedHom.lean)
> (`graphonRootedHom W σ' u v h : PositiveHom σ'`, the rooted conditional homomorphism —
> `φ_W`'s view from a `W`-random root pair), [`GraphonRootedMeasure`](./GraphonRootedMeasure.lean)
> (`rootedViewMeasure_eq_extend`: the rooted-view measure **is** the abstract extension measure
> `ℙ[φ_W]`, via the rooted-vs-unrooted counting bridge `card_stdRooted_class` and
> `measure_eq_of_integral_flag_eq`), and the capstone `GraphonKernelTransport` (the kernel
> dictionary translating rooted 3-vertex flag values into `deg`/`codeg` expressions, transporting
> the `K₄`-free `P₄`-slice equations of [`ParametricP4Slice`](./ParametricP4Slice.lean) into the
> a.e. kernel hypotheses `k4freeP4_graphon_Rtau_eq_zero` / `k4freeP4_graphon_Reta_eq_zero`).
> Tier-2 (the last three theorems inherit the certificate-consumer axioms); everything upstream in
> the stack is Tier-1.

**[`GraphonRepresentation.lean`](./GraphonRepresentation.lean) closes the paper-verbatim form
directly**: **`k4free_p4_tripartite_of_represents`** is the unconditional, paper-verbatim
`thm:k4free-p4-tripartite` (Thm 102) — every graphon *representing* a point of the slice is a.e.
balanced tripartite, with no representation-existence input, since the paper's own quantifier runs
over representatives — plus `k4free_p4_tripartite_of_rep_exists`, the existence form conditional on
the one named classical input `hrep` (Lovász–Szegedy existence). The same pattern closes Cor 106
and Thm 112(iv):

> **`GraphonParametricTransport`/`ParametricStabilityModulus`** — the general-`r` rooted transport
> and the remaining two pieces of §11.8, **`cor:top-endpoint-recovery` (Cor 106)** and
> **`thm:parametric-quant-stability` (iv) (Thm 112(iv))**, are formalised. The `R_τ⁻` kernel
> functional (`Graphon.RtauMinus := ∫∫W(x,y)(d(x)−d(y))²`) is defined with its a.e.
> characterisation, and the **hom→kernel bridge** `graphonHom_f₂_eq_RtauMinus : φ_W(f₂) = R_τ⁻(W)`
> is proved via the extension-measure spec at the edge type — **no new density computations**, the
> same route that discharges the kernel-level third clause of Thm 112(i)
> (`parametricP4_graphon_RtauMinus_le`/`_eq_zero`). The general-`r` rooted transports
> `parametricP4_graphon_Rtau_eq_zero`/`_Reta_eq_zero` mirror the `r = 3` ones; the kernel-level
> Cor 106, `parametricP4_graphon_top_endpoint_rigidity`, shows that slice membership plus the single
> scalar pin `edgeDensity = α_r⁺` — in place of the Zykov equality case — identify the graphon a.e.
> with the balanced complete `r`-partite graphon (`Graphon.slice_rigidity` with all hypotheses
> discharged); `parametricP4_top_endpoint_of_represents`/`_of_rep_exists` package this paper-verbatim,
> mirroring the `GraphonRepresentation` pattern above. Independently,
> `parametric_stability_via_modulus`/`parametric_graphon_stability_via_modulus`
> (`ParametricStabilityModulus.lean`) close Thm 112(iv): the certificate deficit forces the `K₄`
> density near-extremal (`parametricP4_K4_density_approx`), triggering the assumed Zykov stability
> modulus — notably **without using the Zykov bound hypothesis at all** (the `K₄`-density
> approximation drops the certificate's Zykov term without needing its sign, so the modulus itself is
> the only classical content). Both modules are Tier-2 (they consume the certificate-supplied
> slice equations / the `K₄`-density approximation).
>
> **Every numbered result of §11 is formalised**, modulo exactly **four permanent
> named classical inputs** the paper itself cites as external theorems — Erdős–Simonovits stability,
> Zykov's `K₄`-density *bound* (`r ≥ 4`), its *equality case*, and Lovász–Szegedy existence — see
> [Scope & limitations](#scope--limitations). (`paper.tex` §11 has been surgically revised to
> align its statements with the formalisation — Deviation 18.)

Everything here is **machine-checked and `sorry`-free**: "a result is verified" means the Lean
kernel accepts its proof with no `sorry`, `admit`, `native_decide`, or new `axiom` in this
directory. One caveat is inherited rather than local: the §11.6–§11.7 theorems that consume the
`Automation` layer's verified certificate additionally rest on the compiled-evaluation axioms
`Lean.ofReduceBool` / `Lean.trustCompiler` — see [Axioms assumed](#axioms-assumed) (two tiers).

For the dependency structure and a module-by-module map see **[`ARCHITECTURE.md`](./ARCHITECTURE.md)**;
for conventions and a suggested reading order see **[`READING_GUIDE.md`](./READING_GUIDE.md)**.

---

## What is formalised

| Paper result | Statement (informal) | Lean name | Module |
|---|---|---|---|
| §2 `lem:support-as` | a.s. non-negativity ⇔ non-negativity on the support | `ae_nonneg_iff_nonneg_on_support` | [`MeasureSupport`](./MeasureSupport.lean) |
| §3 (quotient algebra) | the constrained algebra `A^σ[T₁]`, the supported space `Q_σ`, and `χ ∈ Q_σ ⇔ χ` vanishes on forbidden flags | `ConstrainedAlgebra`, `Qσ`, `mem_Qσ_iff`, `Qσ_isClosed` | [`ConstrainedClass`](./ConstrainedClass.lean) |
| §3 (faithfulness) | heredity ⟹ the forbidden ideal is the ℝ-span of the forbidden flags | `forbiddenIdeal_eq_span` | [`ForbiddenIdeal`](./ForbiddenIdeal.lean) |
| §3 `lem:support-passes-general` | a random extension of a constrained limit is a.s. constrained: `supp ℙ[φ₀] ⊆ Q_σ` | `support_passes` | [`SupportClosure`](./SupportClosure.lean) |
| §4 `def:root-planting` | `S_σ` (closure of supports of admissible extensions); root-plantable ⇔ `S_σ = Q_σ` | `Sσ`, `RootPlantable` | [`SupportClosure`](./SupportClosure.lean) |
| §4 `thm:support-criterion` | quotient ⇔ ensemble non-negativity for **every** `f` if and only if root-plantable | `support_criterion` | [`SupportClosure`](./SupportClosure.lean) |
| §5 `def:independent-blow-up` | the independent blow-up `G^m`, its projection, `K_r`-freeness preservation | `independentBlowup`, `cliqueFree_independentBlowup` | [`Blowup`](./Blowup.lean) |
| §5 `lem:planted-mass` | a uniform induced embedding of `σ` is *planted* with probability `≥ (λ/2k)^k` | `planted_mass` | [`Blowup`](./Blowup.lean) |
| §5 `lem:planted-estimate` | (equal non-root clones) planted vs base density differ by `≤ 1 − ρ` | `planted_estimate` | [`PlantedEstimate`](./PlantedEstimate.lean) |
| §5 `thm:clone-root-plantable` | clone-closed hereditary classes are root-plantable | `clone_root_plantable` | [`CloneClosed`](./CloneClosed.lean) |
| §5 `cor:clique-free` | `K_r`-free / triangle-free classes are root-plantable | `clique_free_root_plantable`, `clique_free_quotient_iff_ensemble` | [`CloneClosed`](./CloneClosed.lean) |
| §6 `def:complete-blow-up` | the complete blow-up `G^{m,+}` (clique clone classes); the generalised blow-up `subBlowup` | `completeBlowup`, `subBlowup` | [`SubstitutionBlowup`](./SubstitutionBlowup.lean) |
| §6 `lem:true-planted-estimate`, §7 `lem:general-planting-estimate` | the planted mass + estimate carry over to *any* blow-up (the interior is never observed) | `planted_mass_sub`, `planted_estimate_sub` | [`SubstitutionEstimate`](./SubstitutionEstimate.lean) |
| §6 `thm:true-clone-root-plantable` | true-clone-closed hereditary classes are root-plantable | `true_clone_root_plantable`, `true_clone_quotient_iff_ensemble` | [`TrueClone`](./TrueClone.lean) |
| §6 `cor:cluster-graphs` | cluster graphs (`P₃`-free; not clone-closed) are root-plantable | `cluster_root_plantable`, `cluster_quotient_iff_ensemble` | [`ClusterGraph`](./ClusterGraph.lean) |
| §7 `def:substitution-closed` | the substitution `G[H_v]` (= `subBlowup G H`) | `subBlowup`, `SubstitutionClosed` | [`SubstitutionBlowup`](./SubstitutionBlowup.lean), [`Substitution`](./Substitution.lean) |
| §7 `def:blow-up-closed`, `def:vertex-blowup` | the single-vertex blow-up `G[v→H]`; the blow-up-closure property | `oneBlowup`, `BlowupClosed` | [`BlowupClosed`](./BlowupClosed.lean) |
| §7 `lem:blowup-iterate` | single-vertex blow-up closure ⟹ uniform full blow-up in the class | `BlowupClosed.toUniform` | [`BlowupClosed`](./BlowupClosed.lean) |
| §7 `thm:blowup-root-plantable` | **the unified theorem**: blow-up-closed hereditary classes are root-plantable | `blowupClosed_root_plantable` | [`BlowupClosed`](./BlowupClosed.lean) |
| §7 `cor:closures-imply-blowup` | clone- / true-clone- / substitution-closed ⟹ blow-up-closed | `GraphClass.toBlowupClosed`, `TrueCloneClosed.toBlowupClosed`, `SubstitutionClosed.toBlowupClosed` | [`BlowupClosed`](./BlowupClosed.lean), [`TrueClone`](./TrueClone.lean), [`Substitution`](./Substitution.lean) |
| §6 `thm:true-clone-root-plantable`, §7 `thm:substitution-root-plantable` | each a corollary of the unified theorem | `true_clone_root_plantable`, `substitution_root_plantable` | [`TrueClone`](./TrueClone.lean), [`Substitution`](./Substitution.lean) |
| (engine) | root-plantability from any uniform within-class blow-up closure | `subst_root_plantable` | [`SubstitutionClosed`](./SubstitutionClosed.lean) |
| §8 `def:finite-local-planting` | the finite planting property at `σ` | `FinitePlanting` | [`FinitePlanting`](./FinitePlanting.lean) |
| §8 `thm:finite-local-planting` | finite planting at a non-degenerate `σ` ⟹ root-plantable (`S_σ = Q_σ`) | `finitePlanting_root_plantable` | [`FinitePlanting`](./FinitePlanting.lean) |
| §8 `def:sparse-root-repair` | sparse root-blow-up repairs at `σ` | `SparseRootRepair` | [`SparseRootRepair`](./SparseRootRepair.lean) |
| §8 `thm:sparse-repair-planting` | sparse root repairs ⟹ finite planting | `sparseRootRepair_finitePlanting` | [`SparseRootRepair`](./SparseRootRepair.lean) |
| §8 `lem:c5-nbhd` | in a `C₅`-free graph, `e(G[N(v)]) ≤ |N(v)|` | `c5free_neighborhood_edge_card_le` (class `c5FreeClass`) | [`C5Free`](./C5Free.lean) |
| §8 `def:c5-one-root-planting` | the one-root planting `P_L(G,r)` | `oneRootPlant` | [`C5OneRoot`](./C5OneRoot.lean) |
| §8 `lem:c5-planting-free` | `P_L(G,r)` is `C₅`-free | `oneRootPlant_c5free` | [`C5OneRoot`](./C5OneRoot.lean) |
| §8 `lem:c5-one-root-sparse-repair`, `thm:c5-one-root` | the `C₅`-free class is root-plantable at the one-vertex type (`S₁ = Q₁`) | `c5FreeClass_sparseRootRepair_oneVertex`, `c5free_one_root_plantable` | [`C5OneRoot`](./C5OneRoot.lean) |
| §8 `def:c5-nonedge-planting`, `lem:c5-nonedge-planting-free` | two-root non-edge planting `P_L(G,r,s)` and its `C₅`-freeness | `twoRootPlant`, `twoRootPlant_c5free` | [`C5TwoRootNonEdge`](./C5TwoRootNonEdge.lean) |
| §8 `lem:c5-nonedge-sparse-repair`, `thm:c5-nonedge-root` | the `C₅`-free class is root-plantable at the two-root non-edge type (`S_η = Q_η`) | `c5FreeClass_sparseRootRepair_twoNonEdge`, `c5free_two_root_nonedge_plantable` | [`C5TwoRootNonEdge`](./C5TwoRootNonEdge.lean) |
| §8 `lem:c5-blowup` | an independent blow-up of a `C₅`-free graph is `C₅`-free if and only if triangle-free | `c5_blowup_free_iff_triangleFree` | [`C5Blowup`](./C5Blowup.lean) |
| §9 `thm:pinning` | almost-sure pinning plus a quotient point with a different value obstructs root-plantability | `pinning_obstruction` | [`Pinning`](./Pinning.lean) |
| §9 `def:edge-degenerate` | edge-degenerate / co-edge-degenerate classes; the one-root edge flag `e`, unlabelled edge `ρ`; endpoint a.s.-pinning | `EdgeDegenerate`, `CoEdgeDegenerate`, `e`, `ρ`, `ae_e_eq_zero_of_pinned`, `ae_e_eq_one_of_pinned` | [`EdgeObstruction`](./EdgeObstruction.lean) |
| §9 `thm:degenerate-obstruction` | edge-degenerate + arbitrarily large stars ⟹ not root-plantable at the one-vertex type | `degenerate_not_rootPlantable` (concrete), `edgeDegenerate_not_rootPlantable_of_witness` (abstract) | [`StarWitness`](./StarWitness.lean), [`EdgeObstruction`](./EdgeObstruction.lean) |
| §9.1 `lem:c4-edge-zero` | the `C₄`-free class is edge-degenerate (elementary Kővári–Sós–Turán: `(2·e(G))² ≤ 2\|G\|³`) | `c4FreeClass_edgeDegenerate` (bound `c4free_card_edges_sq_le`) | [`C4Free`](./C4Free.lean) |
| §9.1 `cor:c4-counterexample` | `C₄`-free is not root-plantable at the one-vertex type | `c4free_not_rootPlantable` | [`C4Free`](./C4Free.lean) |
| §9.1 `cor:degenerate-family` | general principle: a subquadratic edge bound `e(G) ≤ f(\|G\|)`, `f N/N² → 0`, ⟹ edge-degenerate | `edgeDegenerate_of_subquadratic` | [`DegenerateFamily`](./DegenerateFamily.lean) |
| §9.2 `cor:codegenerate` | the *dense* complement-of-`C₄`-free class is also not root-plantable (density is not the dividing line) | `coDegenerate_not_rootPlantable`, `coC4free_not_rootPlantable`, `CoEdgeDegenerate`, `coEdgeDegenerate_not_rootPlantable_of_witness` (abstract) | [`StarWitness`](./StarWitness.lean), [`DenseObstruction`](./DenseObstruction.lean), [`EdgeObstruction`](./EdgeObstruction.lean) |
| §9.2 `lem:complementation` | root-plantability is invariant under graph complementation: `RootPlantable (K.σ) ↔ RootPlantable (K̄.σᶜ)` | `complementation_invariance`, `complementation_invariance_oneVertex` (`HeredClass.compl`, `complHomeo`, pushforward `complHomeo_map_eq`, density identity `flagDensity₁_compl`) | [`FlagComplement`](./FlagComplement.lean), [`ComplementHom`](./ComplementHom.lean), [`ComplementClass`](./ComplementClass.lean), [`ComplementInvariance`](./ComplementInvariance.lean) |
| §9.4 `subsec:boundary` (edge-deletion closure) | every spanning subgraph of an in-class graph is in-class | `EdgeDeletionClosed` | [`NoInterior`](./NoInterior.lean) |
| §9.4 (edge-thinning realization) | a deterministic in-class spanning subgraph tracking the Bernoulli-thinned expectations within `ε` (variance/Chebyshev + union bound) | `exists_thinned_realization` | [`EdgeThinning`](./EdgeThinning.lean) |
| §9.4 (edge-thinned limit) | the edge-thinned constrained limit `φ₀^λ ∈ Q₀`, with σ-density `≥ λ^{e(σ)}·φ₀⟨σ⟩₀ > 0` | `exists_thinned_limit` | [`EdgeThinningLimit`](./EdgeThinningLimit.lean) |
| §9.4 (boolean cloud point) | the `{0,1}`-valued "edgeless cloud" profile lies in `S_σ` | `exists_boolean_point_in_Sσ` | [`NoInteriorThinning`](./NoInteriorThinning.lean) |
| §9.4 `thm:no-interior` | a σ-flag pinned to `c` on `S_σ` for an edge-deletion-closed class has `c ∈ {0,1}` (no interior pinning) | `no_interior_pinning` | [`NoInteriorThinning`](./NoInteriorThinning.lean) |
| §9.5 `lem:c5-few-triangles` | for `C₅`-free `G`, `3·T(G) ≤ 2·e(G)` (via `3·T(G) = ∑_v e(G[N(v)])`) | `c5free_three_mul_triangle_le` (count `three_mul_card_cliqueFinset_three_eq`) | [`C5FewTriangles`](./C5FewTriangles.lean) |
| §9.5 `cor:c5-edge-pinned` | the common-neighbour triangle flag `F_△` is a.s. pinned to `0` under random edge-rooting | `ae_Ftri_eq_zero_of_pinned` | [`C5EdgeObstruction`](./C5EdgeObstruction.lean) |
| §9.5 `def:c5-book` / `lem:c5-book` | the `C₅`-free **book graph**, with `F_△`-density `1` | `bookLabeled`, `book_c5free`, `book_Ftri_density` | [`C5EdgeObstruction`](./C5EdgeObstruction.lean) |
| §9.5 `cor:c5-no-pin` | no obstruction at the vertex type: triangle-over-vtype density `0` on `Q_vtype`, edge not pinned | `c5free_triOverVtype_zero_on_Qvtype`, `c5free_edge_not_pinned` | [`C5EdgeObstruction`](./C5EdgeObstruction.lean) |
| §9.5 `thm:c5-edge-not-root-plantable` | the `C₅`-free class is **not** root-plantable at the two-root edge type (refuting the all-types conjecture) | `c5free_edge_not_rootPlantable` | [`C5EdgeObstruction`](./C5EdgeObstruction.lean) |
| §10 (engine) | the master evaluation bound `\|s\| ≤ δ` on `S_σ` ⟹ `\|φ₀ ⟦s⟧₀\| ≤ δ` on `Q₀`; degenerate types kill all unlabelled averages; a singleton `S_σ` collapses them | `abs_downward_eval_le_of_abs_le_on_Sσ`, `downward_eval_eq_zero_of_degenerate`, `downward_eval_eq_of_Sσ_singleton` | [`DownwardAverage`](./DownwardAverage.lean) |
| §10 `prop:empty-type` | the empty-type extension is Dirac (`Ext_∅(φ₀) = δ_{φ₀}`), `S_∅ = Q₀`, and the empty type is **always** root-plantable | `extend_emptyType_eq_dirac`, `Sσ_emptyType_eq`, `emptyType_rootPlantable`, `heredClass_emptyType_rootPlantable`, `emptyType_quotient_iff_ensemble` | [`EmptyTypeCollapse`](./EmptyTypeCollapse.lean) |
| §10 `cor:confined` | no empty-type density bound is ensemble-true but quotient-false | `ensemble_implies_quotient_emptyType` | [`EmptyTypeCollapse`](./EmptyTypeCollapse.lean) |
| §10 `thm:no-closed-certificate-gap` | the quotient (sums-of-squares) and ensemble (non-negative on `S_σ`) certificate cones have the same `Q₀`-seminorm closure, for **every** type | `quotCone`, `ensCone`, `ensCone_subset_closure_quotCone`, `no_closed_certificate_gap` | [`CertificateCones`](./CertificateCones.lean) |
| §10 `prop:ideal-zero` | elements vanishing on `S_σ` — pinning witnesses and their flag-multiples — unlabel to zero on `Q₀` | `downward_eval_eq_zero_of_zero_on_Sσ`, `pinned_witness_downward_eq_zero`, `downward_eval_congr_of_eqOn_Sσ` | [`VanishingIdeal`](./VanishingIdeal.lean) |
| §10 (limit points) | the labelled empty-graph / complete-graph limits in `X_vtype`, unique with their vanishing patterns | `edgelessPoint`, `completePoint`, `eq_edgelessPoint_of_nonEdgeless_zero`, `eq_completePoint_of_nonComplete_zero` | [`BooleanPoint`](./BooleanPoint.lean) |
| §10 `prop:single-point` | for an (co-)edge-degenerate class, `S_vtype` is a single point and both certificate cones collapse to the ray `ℝ≥0·1₀` | `Sσ_eq_singleton_of_edgeDegenerate` / `_coEdgeDegenerate`, `edgeDegenerate_cone_collapse` / `coEdgeDegenerate_cone_collapse` | [`SinglePoint`](./SinglePoint.lean) |
| §10 `cor:c5-edge-closed-inert` | the `C₅`-free edge-type gap is closed-cone inert: the ensemble relaxation improves no asymptotic `C₅`-free density bound | `c5free_edge_no_closed_certificate_gap`, `c5free_Ftri_zero_on_Sσ`, `c5free_Ftri_mul_downward_eq_zero` | [`C5EdgeInert`](./C5EdgeInert.lean) |
| §11.2 (relative supports) | the relative labelled support `S_σ(Y)` over an arbitrary set `Y` of admissible limits; `Y = Q₀` recovers the absolute `S_σ` | `relSσ`, `support_subset_relSσ`, `relSσ_mono`, `Sσ_eq_relSσ` | [`RelativeSupport`](./RelativeSupport.lean) |
| §11.2 `prop:relative-soundness` | `f ≥ 0` on `S_σ(Y)` ⟹ `φ₀ ⟦f⟧₀ ≥ 0` for every `φ₀ ∈ Y` (degenerate types included) | `relative_soundness` | [`RelativeSupport`](./RelativeSupport.lean) |
| §11.2 `prop:relative-criterion` | non-negativity on `S_σ(Y)` ⇔ a.s. non-negativity under every admissible extension — **unconditionally** (the relative analogue of root-plantability is automatic) | `relative_criterion`, `RelEnsembleNonneg` | [`RelativeSupport`](./RelativeSupport.lean) |
| §11.2 `lem:relative-closure` | closing the constraint set does not change the support: `S_σ(closure Y) = S_σ(Y)` | `relSσ_closure_eq` (via weak continuity `extend_tendsto` and support lower-semicontinuity `support_subset_closure_iUnion_support`) | [`RelativeClosure`](./RelativeClosure.lean) |
| §11.3 `thm:relative-slackness` (+ `rem:cs-shape` square instances) | **the §11 workhorse**: a relative certificate yields soundness, approximate slackness (`Δ`-bounds per term), exact slackness on the equality slice (incl. a.s. vanishing), and global vanishing on `S_σ(Y)`; for `fᵢ = l·l` the exact/global conclusions read `ψ(l) = 0` a.s. / `l = 0` on `S_{σᵢ}(Y)` | `relative_slackness_soundness` / `_approx` / `_term` / `_slack` / `_exact_slack` / `_exact_term` / `_exact_ae` / `_global` / `_exact_ae_sq` / `_global_sq` | [`RelativeSlackness`](./RelativeSlackness.lean) |
| §11.3 `lem:relative-cauchy-schwarz` | Cauchy–Schwarz for unlabelled averages: `(φ₀ ⟦l·g⟧₀)² ≤ φ₀ ⟦l·l⟧₀ · φ₀ ⟦g·g⟧₀` | `downward_cauchy_schwarz` (+ `downward_sq_eval_nonneg`) | [`RelativeSlackness`](./RelativeSlackness.lean) |
| §11.3 `cor:sos-first-moments` | certificates control first moments at rate `√Δ` (stated in the equivalent squared form) | `certificate_first_moment_sq_bound`, `certificate_first_moment_sq_bound_one` | [`RelativeSlackness`](./RelativeSlackness.lean) |
| §11.3 `prop:unique-slice-stability` | a slice consisting of a single limit upgrades to qualitative stability, by compactness alone | `unique_slice_stability` | [`RelativeSlackness`](./RelativeSlackness.lean) |
| §11.3 `thm:kernel-slackness` | the matrix form: a PSD block certificate `⟨Q v, v⟩` is consumed directly (no eigendecomposition); on the equality slice the labelled moment vector falls into `ker Q`, a.s. and on all of `S_σ(Y)` | `kernel_slackness_soundness` / `_approx` / `_exact_slack` / `_exact_ae` / `_global` (+ `kernelCombo`, `eval_flagQuadraticForm`, `posSemidef_dotProduct_mulVec_sq_le`) | [`KernelSlackness`](./KernelSlackness.lean) |
| §11.4 `def:relative-plantability` (Def 84) | the relative planted set `Q_σ(Y)` (density limits of in-class σ-flags whose unlabelled limits fall in `closure Y`) and relative root-plantability `S_σ(Y) = Q_σ(Y)` | `relQσ`, `RelativelyRootPlantable` | [`RelativePlanted`](./RelativePlanted.lean) |
| §11.4 `prop:relative-plantability` (Prop 85) | structure of the planted set: closed, `⊆ Q_σ`, `⊇ supp ℙ[φ₀]` and `⊇ S_σ(Y)`, `Y = Q₀` recovers absolute root-plantability, and the relative planted criterion (non-negativity on `Q_σ(Y)` ⇔ relative ensemble semantics for every `f`, iff relatively root-plantable) | `relQσ_isClosed`, `relQσ_subset_Qσ`, `support_subset_relQσ`, `relSσ_subset_relQσ`, `relQσ_Q0_eq`, `relativelyRootPlantable_Q0_iff`, `relQσ_nonneg_implies_relEnsemble`, `relative_planted_criterion` | [`RelativePlanted`](./RelativePlanted.lean) |
| §11.4 `prop:mantel-not-plantable` (Prop 86) | the Mantel slice breaks relative root-plantability: `S_vtype(Y_Mantel) ⊊ Q_vtype(Y_Mantel)` (witness = parity-bipartite `K_{n+1,n+1}` + isolated root, Deviation 14g). The raw pinning hypothesis `hpin` (Thm 92(i)) is now **discharged**: `mantel_not_relatively_plantable_of_uniqueness` needs only the named Erdős–Simonovits hypothesis `hES` (the original `hpin`-form remains too) | `mantel_not_relatively_plantable` (`hpin`-form), `mantel_not_relatively_plantable_of_uniqueness` (`hES`-form), `exists_mantel_planted_view_edge_zero`, `knnPlusW` | [`MantelNotPlantable`](./MantelNotPlantable.lean), [`TuranSliceIdentities`](./TuranSliceIdentities.lean) |
| §11.4 `thm:relative-certificate-gap` (Thm 88) | no closed certificate gap over a slice: the quotient SOS cone and the relative ensemble cone have the same `‖·‖_Y`-closure | `no_relative_closed_certificate_gap` (+ `YWithin`, `MemYClosure`, `relEnsCone`) | [`RelativeCertificateGap`](./RelativeCertificateGap.lean) |
| §11.4 `thm:relative-positivstellensatz` (Thm 89) | slice-valid density bounds are whole-class-provable up to `ε·1₀`, with a finite penalty `M·∑ gⱼ²`; cone form: the `Y`-non-negative elements are the `‖·‖_{Q₀}`-closure of `C_{Q₀} + span{gⱼ²}` | `relative_positivstellensatz`, `relative_positivstellensatz_closure` | [`RelativePositivstellensatz`](./RelativePositivstellensatz.lean) |
| §11.5 `thm:turan-slice` (Thm 91) | the **existence half** (unconditional: the Turán slice `Y_Tur^{(r)}` is nonempty, witnessed by the balanced `r`-partite limit) **plus the full identity halves (i)–(iii)** under the single named Erdős–Simonovits hypothesis `hES : turanSlice r ⊆ {posHomPoint (turanLimit r hr)}` — equivalent to the paper's "consists of exactly one point", since `turanLimit_mem_slice` gives the reverse inclusion unconditionally. Values: `e = (r-1)/r` at `vtype`; `a_τ = b_τ = 1/r`, `g_τ = (r-2)/r`, `z_τ = 0` at `FlagType_2_1`; `z_η = 1/r`, `g_η = (r-1)/r`, `a_η = b_η = 0` at `FlagType_2_0`. Only ES itself remains a classical input (Deviation 15) | `turanSlice`, `turanSlice_nonempty`, `exists_turan_limit`; `turanLimit`, `turanLimit_mem_slice`, `turanLimit_relSσ_vtype`/`_edge`/`_nonEdge`, `turan_slice_identity_vtype`/`_edge`/`_nonEdge` | [`TuranLimit`](./TuranLimit.lean), [`TuranAut`](./TuranAut.lean), [`TuranDirac`](./TuranDirac.lean), [`TuranSliceIdentities`](./TuranSliceIdentities.lean) |
| §11.5 `thm:relative-mantel` (Thm 92) | likewise at `r = 2` (the Mantel slice): existence unconditional, and — under `hES` — clause (i), the relative-support edge pinning at `1/2` (`relative_mantel_vtype`, exactly `MantelNotPlantable`'s `hpin`); the `τ`/`η` clauses are the `r = 2` instances of the parametric identities | `mantelSlice`, `mantelSlice_nonempty`, `relative_mantel_vtype` | [`TuranLimit`](./TuranLimit.lean), [`TuranSliceIdentities`](./TuranSliceIdentities.lean) |
| §11.6 `prop:equality-slice-vanishing` (Prop 94) | equality slices force certificate terms to vanish: a certificate `h + ∑ λᵢ ⟦ℓᵢ²⟧₀ ≤ c·1₀` on `Q₀` makes every `ℓᵢ` vanish identically on `S_{σᵢ}(Y)` over the slice `Y = {φ₀ : φ₀ h = c}` | `equality_slice_vanishing`, `eqSlice` | [`CertificateSliceVanishing`](./CertificateSliceVanishing.lean) |
| §11.6 `thm:k4free-p4-equality-slice` (Thm 95) | the `K₄`-free `P₄` equality-slice equations at the non-edge/edge types — **unconditional at `r = 3`** (no Zykov input) | `k4freeP4_eta_equation`, `k4freeP4_tau_symm`, `k4freeP4_tau_equation`, `k4freeP4Slice` (`k4freeP4Slice_eq_parametric`) | [`ParametricP4Slice`](./ParametricP4Slice.lean) |
| §11.6 `thm:parametric-p4-equality-slice` (Thm 97) | the parametric slice equations `(r-1)·z_η = g_η`, `a_τ = b_τ`, `(r-2)(a_τ+b_τ) = 2g_τ`, and the extremal `K₄` density on `Y_r` (Zykov bound as the explicit hypothesis `hZykov` — Deviation 14a; the paper's restated Thm 97 now names this bound explicitly for `r ≥ 4` too, matching `hZykov` here — Deviation 18) | `parametricP4_eta_equation`, `parametricP4_tau_symm`, `parametricP4_tau_equation`, `parametricP4_K4_density` | [`ParametricP4Slice`](./ParametricP4Slice.lean) |
| §11.7 `thm:parametric-moments` (Thm 99) | the exact kernel-level moment identities `(r-1)T = (r-2)D`, `r(2r-3)D = (r-1)²(3p-1)`, the variance factorisation, the interval `α⁻ ≤ p ≤ α⁺` with regularity at the endpoints (on `unitInterval` graphons — Deviation 14b) | `Graphon.moments_T` / `_D` / `_variance` / `_interval` / `_regular_iff` | [`GraphonMoments`](./GraphonMoments.lean) |
| §11.7 `thm:slice-rigidity` (Thm 100) | rigidity at the regular endpoint: the two mined local equations at `p = (r-1)/r` force the balanced complete `r`-partite graphon, in measurable-partition form (`P : I → Fin r`, fibers of volume `1/r`, `W = 0/1` by block a.e. — Deviation 14c) | `Graphon.slice_rigidity` | [`GraphonRigidity`](./GraphonRigidity.lean) |
| §11.7 `cor:r3-rigidity` (Cor 101) | unconditional rigidity at `r = 3` (the two endpoints coincide, so no edge-density hypothesis) | `Graphon.r3_rigidity` | [`GraphonRigidity`](./GraphonRigidity.lean) |
| §11.7 `cor:k4free-p4-qualitative-stability` (Cor 104) | qualitative stability for the `K₄`-free `P₄` problem (singleton slice identification as the explicit hypothesis `huniq` — its content is Thm 102, whose kernel engine `r3_rigidity` **is** formalised) | `k4free_qualitative_stability` | [`SliceRecovery`](./SliceRecovery.lean) |
| §11.7 `cor:parametric-p4-turan-recovery` (Cor 105) | the recovery half: Zykov equality (`hZykEq` hypothesis) collapses the parametric slice to `{χ★}`; **and** the "consequently" support identities at all three types (Tier-2, inherited via `parametric_recovery`). Benign deviation: Lean assumes `3 ≤ r` where the paper says `r ≥ 4` — a hypothesis weakening (at `r = 3` the `hZykEq` input degenerates but the statement stays sound as a conditional; Deviation 15c) | `parametric_recovery`, `parametric_recovery_identities` | [`SliceRecovery`](./SliceRecovery.lean), [`TuranSliceIdentities`](./TuranSliceIdentities.lean) |
| §11.7 `cor:top-endpoint-recovery` (Cor 106) | the single scalar pin `edgeDensity = α_r⁺` — in place of the Zykov equality case — identifies a representing graphon a.e. with the balanced complete `r`-partite graphon: the kernel-level rigidity (`Graphon.slice_rigidity` with all hypotheses discharged), the paper-verbatim representative-quantified form (unconditional, no representation-existence input, mirroring Thm 102's `k4free_p4_tripartite_of_represents`), and the `hrep`-conditional existence form. Stated at `3 ≤ r` (benign generalisation, same pattern as Cor 105 — Deviation 15c) | `parametricP4_graphon_top_endpoint_rigidity`, `parametricP4_top_endpoint_of_represents`, `parametricP4_top_endpoint_of_rep_exists` | [`GraphonParametricTransport`](./GraphonParametricTransport.lean) |
| §11.7 `cor:parametric-qualitative-stability` (Cor 107) | parametric qualitative stability: extremal `P₄`-density sequences converge to the balanced `r`-partite limit (under `hZykov`/`hZykEq`/`hne`) | `parametric_qualitative_stability` | [`SliceRecovery`](./SliceRecovery.lean) |
| §11.8 `thm:approximate-moments` (Thm 109) | the approximate moment identities, certificate-free, for **every** graphon: deviation `≤ (r-1)√R_η + ((r-2)/2)√R_τ` | `Graphon.approximate_moments` (`_interval` / `_variance`) | [`GraphonMoments`](./GraphonMoments.lean) |
| §11.8 `prop:k4free-p4-certificate-stability` (Prop 110) | the hom level: the certificate square bounds (the `9/8`, `1/5`, `9/35` pattern after dividing by the coefficients); **the `R_τ⁻` kernel functional is now defined** (`Graphon.RtauMinus := ∫∫W(d(x)−d(y))²`, with its a.e. characterisation), and its bound against `Δ` is now proved at the kernel level via the hom→kernel bridge `graphonHom_f₂_eq_RtauMinus`, rather than entering `GraphonQuantStability` as a bare hypothesis | `parametricP4_sq_bounds`; `Graphon.RtauMinus`, `graphonHom_f₂_eq_RtauMinus`, `parametricP4_graphon_RtauMinus_le`/`_eq_zero` | [`ParametricP4Slice`](./ParametricP4Slice.lean), [`GraphonParametricTransport`](./GraphonParametricTransport.lean) |
| §11.8 `thm:k4free-p4-quant-stability` (Thm 111) | the `r = 3` quantitative chain: `(3p-2)² ≤ C`, degree concentration, the `Δ^{1/4}` edge-density stability, the certificate instance, and the final modulus implication (`ω_Tur` abstracted as a target-predicate modulus; `δ□` not formalised — Deviation 14d) | `Graphon.r3_edge_sq_bound`, `r3_degree_concentration`, `r3_edge_density_stability`, `r3_certificate_instance`, `stability_via_modulus` | [`GraphonQuantStability`](./GraphonQuantStability.lean) |
| §11.8 `thm:parametric-quant-stability` (Thm 112) | (i) hom level: the square bounds, plus the kernel-level third clause `p₂(r)·R_τ⁻(W) ≤ Δ`; (ii) hom level: the approximate `K₄` density — notably **without** Zykov input; (iii) both sides: quadratic confinement and interval localisation (both halves); (iv) the `ω_Zyk` route is **now formalised** — notably, also **without** needing the Zykov bound hypothesis (the `K₄`-density approximation drops the certificate's Zykov term without using its sign, so the modulus `hmod` is the only classical content) | (i) `parametricP4_sq_bounds`, `parametricP4_graphon_RtauMinus_le`; (ii) `parametricP4_K4_density_approx`; (iii) `Graphon.interval_localisation` / `_below` (+ `quadratic_confinement`, `moment_deviation_bound`); (iv) `parametric_stability_via_modulus`, `parametric_graphon_stability_via_modulus` | [`ParametricP4Slice`](./ParametricP4Slice.lean), [`GraphonQuantStability`](./GraphonQuantStability.lean), [`GraphonParametricTransport`](./GraphonParametricTransport.lean), [`ParametricStabilityModulus`](./ParametricStabilityModulus.lean) |

A **new supporting theorem** that does not appear as a numbered result in the paper but is the
foundational input to `thm:clone-root-plantable`:

| | Statement | Lean name | Module |
|---|---|---|---|
| Constrained representation theorem | a positive hom vanishing on all forbidden flags is the density limit of a sequence of **forbidden-free** flags (a *constrained* refinement of Razborov 3.3(b)) | `exists_constrained_flagSeq_limit` | [`ConstrainedRep`](./ConstrainedRep.lean) |

§1 (Introduction) is prose and has nothing to formalise. **§6 (complete blow-ups / true twins)
and §7 (substitution-closed classes) are also formalised** (table above), reusing the §5 machinery
through the generalised blow-up `subBlowup`; **§8 (finite local planting and the `C₅`-free class) is
formalised too**, reusing the §5/§7 capstone toolkit (see the §8 rows above and Deviation 8).
**All of §9 (§9.1–§9.5) is formalised** (the abstract pinning obstruction `thm:pinning`, the
degeneracy obstruction `thm:degenerate-obstruction`, the `C₄`-free counterexample `lem:c4-edge-zero` /
`cor:c4-counterexample`, the general family criterion `cor:degenerate-family`, the dense
counterpart `cor:codegenerate`, the §9.4 boundary / no-interior theorem `thm:no-interior`, and the
§9.5 `C₅`-edge obstruction `thm:c5-edge-not-root-plantable` with `lem:c5-few-triangles` and the
book-graph quotient point), reusing the §5/§8 constrained-representation and class machinery;
**`lem:complementation`** (complementation invariance of root-plantability) is formalised too, via
the complement homeomorphism (Deviation 9b). **All of §10 ("the gap is invisible to density
bounds") is formalised** (the empty-type collapse `prop:empty-type` / `cor:confined`, the
closed-cone equality `thm:no-closed-certificate-gap`, the vanishing ideal `prop:ideal-zero`, the
single-point collapse `prop:single-point`, and the `C₅`-edge inertness `cor:c5-edge-closed-inert`) —
see the §10 rows above and Deviation 12. **§11.1 is prose** (it points back to the already-formalised
§5–§8 criteria), and **the foundational §11.2–§11.3 relative theory is formalised** (the relative
support `S_σ(Y)` with `lem:relative-closure` / `prop:relative-soundness` / `prop:relative-criterion`,
and the complementary-slackness principle `thm:relative-slackness` with `lem:relative-cauchy-schwarz`,
`cor:sos-first-moments`, `thm:kernel-slackness`, `prop:unique-slice-stability`) in the
`RelativeSupport`/`RelativeClosure`/`RelativeSlackness`/`KernelSlackness` modules (Deviation 13).
**§11.4–§11.8 — the slice method and the graphon layer — is now formalised in full** (the rows
above; Deviations 14–15, 18): §11.4 in full
(`def:relative-plantability`/`prop:relative-plantability`/`prop:mantel-not-plantable`/
`thm:relative-certificate-gap`/`thm:relative-positivstellensatz`), the §11.5 Turán/Mantel slice
theorems (existence unconditional; the identity halves under the named Erdős–Simonovits
hypothesis `hES`, via the transitivity→Dirac route of the
`TuranAut`/`TuranDirac`/`TuranSliceIdentities` stack — Deviation 15), the §11.6 equality-slice
results (`prop:equality-slice-vanishing`
and the two `P₄` slice theorems, fed by the verified `CompleteGraphFreeP4.gap_identity`
certificate), the §11.7–§11.8 kernel-level moment / rigidity / quantitative-stability theorems in a
self-contained graphon layer, and the recovery / qualitative-stability corollaries with classical
inputs as named hypotheses (Deviation 14a) — Cor 105 is complete, including its
"consequently" support identities (`parametric_recovery_identities`). The rooted transport
(`HOM_TO_GRAPHON_DESIGN.md`, five modules ending at `GraphonKernelTransport`)
carries the `K₄`-free `P₄`-slice equations all the way to `Graphon.r3_rigidity`'s a.e. kernel
hypotheses, discharging both of them (`k4freeP4_graphon_tripartite`) — the graphon-side content of
`thm:k4free-p4-tripartite` (Thm 102). **[`GraphonRepresentation.lean`](./GraphonRepresentation.lean)
then closes Thm 102 itself**: `k4free_p4_tripartite_of_represents` is the unconditional,
paper-verbatim statement (the paper's own quantifier runs over *representing* graphons, so no
representation-existence input is needed), plus `k4free_p4_tripartite_of_rep_exists` conditional on
the one named classical input `hrep` (Lovász–Szegedy existence). The same route closes the two
remaining pieces: Cor 106 (`GraphonParametricTransport.lean`'s `parametricP4_top_endpoint_of_represents` /
`_of_rep_exists`) and Thm 112(iv) (`ParametricStabilityModulus.lean`'s
`parametric_stability_via_modulus`). **Every numbered result of §11 is formalised**, modulo
exactly the four permanent named classical inputs of [Scope & limitations](#scope--limitations) —
Erdős–Simonovits stability, Zykov's `K₄`-density bound and its equality case, and
Lovász–Szegedy existence (`hrep`, retirable only by the costed weak-regularity campaign of
`HOM_TO_GRAPHON_DESIGN.md`). (`SliceRecovery`'s `huniq` hypothesis for Cor 104 is a separate,
optional-to-retire hom-level shortcut, untouched by this closure.) The
only §9 result still open is the general pinning *conjecture* `conj:characterisation` — see
[Scope & limitations](#scope--limitations).

A note on how to read the §8 rows against the paper, and what to scrutinise when checking the
correspondence by hand, is in [Auditing the correspondence to `paper.tex`](#auditing-the-correspondence-to-papertex) below.

---

## Status & verification

* **`sorry`-free.** No `sorry`/`admit`/`native_decide` appears in any module, and there are no
  `axiom` declarations.
* **Axiom-clean.** Every capstone theorem — the unified `blowupClosed_root_plantable`, the §5
  `clone_root_plantable` / `clique_free_root_plantable` / `clique_free_quotient_iff_ensemble`, the
  §6–§7 `true_clone_root_plantable` / `substitution_root_plantable` / `cluster_root_plantable`, and
  the §8 `finitePlanting_root_plantable` / `sparseRootRepair_finitePlanting` /
  `c5free_one_root_plantable` / `c5free_two_root_nonedge_plantable`, and the §9 `pinning_obstruction`
  / `degenerate_not_rootPlantable` / `c4free_not_rootPlantable` / `coDegenerate_not_rootPlantable` /
  `coC4free_not_rootPlantable` / `edgeDegenerate_of_subquadratic` / `complementation_invariance` /
  `no_interior_pinning` / `c5free_edge_not_rootPlantable`, and the §10
  `emptyType_rootPlantable` / `heredClass_emptyType_rootPlantable` / `extend_emptyType_eq_dirac` /
  `no_closed_certificate_gap` / `downward_eval_eq_zero_of_zero_on_Sσ` /
  `Sσ_eq_singleton_of_edgeDegenerate` / `Sσ_eq_singleton_of_coEdgeDegenerate` /
  `edgeDegenerate_cone_collapse` / `coEdgeDegenerate_cone_collapse` /
  `c5free_edge_no_closed_certificate_gap`, and the §11.2–§11.3 `relSσ_closure_eq` /
  `relative_soundness` / `relative_criterion` / the full `relative_slackness_*` family /
  `downward_cauchy_schwarz` / `certificate_first_moment_sq_bound(_one)` / `unique_slice_stability` /
  the full `kernel_slackness_*` family, and the §11.4–§11.8 `relative_planted_criterion` /
  `relative_positivstellensatz(_closure)` / `no_relative_closed_certificate_gap` /
  `mantel_not_relatively_plantable` / `equality_slice_vanishing` / `exists_turan_limit` /
  `turanSlice_nonempty` / the §11.5 Turán slice-identity family (`turanLimit_relSσ_vtype`/`_edge`/
  `_nonEdge`, `turan_slice_identity_vtype`/`_edge`/`_nonEdge`, `relative_mantel_vtype`,
  `mantel_not_relatively_plantable_of_uniqueness`) / the whole `Graphon.*` layer (`moments_*`,
  `approximate_moments*`,
  `slice_rigidity`, `r3_rigidity`, the quantitative-stability chain), and the new §11.7 `φ_W`
  construction (`graphonHom`, `graphonProfile_zeroSpaceProp`/`_oneProp`/`_mulProp`,
  `graphonHom_edge`, and the induced-density/subset-count lemmas of
  `GraphonInducedDensity`/`PairSubsetCount`/`EmptyTypeGraphBridge`) —
  depends on **only the three standard Mathlib axioms** `[propext, Classical.choice, Quot.sound]` —
  no `sorryAx`. **The one exception (Tier 2):** the theorems consuming the verified parametric
  certificate `CompleteGraphFreeP4.gap_identity` — the `parametricP4_*` / `k4freeP4_*` slice
  equations and `SliceRecovery`'s `parametric_recovery` / `parametric_qualitative_stability`, plus
  `parametric_recovery_identities` (which inherits through `parametric_recovery`),
  `GraphonKernelTransport`'s `k4freeP4_graphon_Rtau_eq_zero` / `k4freeP4_graphon_Reta_eq_zero` /
  `k4freeP4_graphon_tripartite` (which inherit through the `k4freeP4_*` slice equations they
  transport into kernel form), `GraphonRepresentation`'s `k4free_p4_tripartite_of_represents` /
  `k4free_p4_tripartite_of_rep_exists` (which inherit through `k4freeP4_graphon_tripartite`), and now
  `GraphonParametricTransport`'s `parametricP4_graphon_Rtau_eq_zero` / `_Reta_eq_zero` /
  `_RtauMinus_le` / `_RtauMinus_eq_zero` / `_top_endpoint_rigidity` /
  `parametricP4_top_endpoint_of_represents` / `_of_rep_exists`, plus
  `ParametricStabilityModulus`'s `parametric_stability_via_modulus` /
  `parametric_graphon_stability_via_modulus` (which inherit through `parametricP4_sq_bounds` /
  `parametricP4_K4_density_approx`) —
  additionally depend on `[Lean.ofReduceBool, Lean.trustCompiler]`, *inherited* from the
  `Automation` layer's `native_decide` bridges, not from any `native_decide` here; see
  [Axioms assumed](#axioms-assumed).
* **Builds.** `lake build LeanFlagAlgebras.MetaTheory` compiles all 95 modules (8018 jobs); the full
  project `lake build LeanFlagAlgebras` builds with §9–§11.8 integrated.
* **One non-default option.** Two §8 declarations carry `set_option maxHeartbeats …` (1000000 on
  `sparseRootRepair_finitePlanting`, 800000 on `c5FreeClass_sparseRootRepair_oneVertex`) — a raise of
  the elaboration step budget for proofs run in a large local context. This affects *how long* the
  kernel is willing to check, not *what* it checks: it is not `native_decide` and introduces no
  axiom; the `#print axioms` output above is unaffected.
* **Warning-clean, modulo six intentional warnings.** A `lake build` of the layer emits exactly six
  linter warnings, all deliberately retained: `BinomialRatio.hr` and `C5TwoRootNonEdge.hrs` are
  paper-faithful statement hypotheses that the proof happens not to use (part of the stated setup;
  `hrs` is Deviation 8d); three unused-section-variable warnings live in the superseded, off-critical-path
  `ProductTV` (Deviation 1), left untouched; and one is an unused bound-variable name inside a
  `∀`-type in a public `SubstitutionClosed` statement. None indicates an incomplete or incorrect
  proof.

### Axioms assumed

The development has **two axiom tiers**, and which tier a theorem sits in is checked mechanically
by `#print axioms <name>`.

#### Tier 1 — everything except the certificate consumers listed under Tier 2

Every theorem outside Tier 2 is proved from **exactly the three axioms of Mathlib's classical
foundation, and nothing else**:

| Axiom | What it asserts | Why it is trusted |
|---|---|---|
| `propext` | *propositional extensionality* — two propositions that imply each other are equal (`(a ↔ b) → a = b`). | Part of Lean 4 core; standard classical logic, consistent with Lean's type theory. |
| `Classical.choice` | *the axiom of choice* — a nonempty type has a distinguished element. | The basis of classical reasoning (excluded middle, `Classical.em`, decidability of every proposition) throughout Mathlib. |
| `Quot.sound` | *soundness of quotients* — related elements have equal quotient images. | Part of Lean 4 core; what makes quotient types (used pervasively here — `FlagAlgebra σ` is a quotient) compute correctly. |

These three are the axioms underlying essentially all of Mathlib; a proof that depends only on them
is as trustworthy as the Lean/Mathlib platform itself. What matters for *this* formalisation is the
**absence** of anything else, checked mechanically by `#print axioms`:

* **No `sorryAx`.** `sorryAx` is the axiom Lean inserts for a `sorry`/`admit`; its absence from the
  `#print axioms` output of every headline theorem certifies there is no hidden gap. (`grep` for the
  tokens `sorry`/`admit` is a syntactic check; the `#print axioms` `sorryAx` check is the semantic
  one, and also catches a `sorry` reached *transitively* through any dependency.)
* **No `native_decide`.** `native_decide` would add the `Lean.ofReduceBool` axiom and move part of
  the proof into compiled native code (outside the kernel); it is used **nowhere in `MetaTheory`**.
  (Tier 2's extra axioms are *inherited* through an import from the `Automation` layer, not
  produced by anything in this directory.)
* **No project `axiom` declarations.** This development declares no axioms of its own; the base
  `LeanFlagAlgebras/FlagAlgebra/` library it builds on is likewise `sorry`-free Lean, not a set of
  postulated axioms.

So for Tier 1 the trusted base is precisely *Lean 4 + Mathlib's three classical axioms* — the
reader need not trust any bespoke assumption. The
[verification recipe below](#how-to-verify-it-yourself) reproduces the `#print axioms` output for
the headline theorems of every section.

#### Tier 2 — the verified-certificate consumers (`+ Lean.ofReduceBool, Lean.trustCompiler`)

**Exactly** the theorems consuming the verified parametric certificate
`CompleteGraphFreeP4.gap_identity` (from the repository's `Automation` layer) — namely
`ParametricP4Slice`'s `parametricP4_cert` / `parametricP4_eta_equation` / `parametricP4_tau_symm` /
`parametricP4_tau_equation` / `parametricP4_K4_density` / `parametricP4_sq_bounds` /
`parametricP4_K4_density_approx`, its `r = 3` forms `k4freeP4_eta_equation` / `k4freeP4_tau_symm` /
`k4freeP4_tau_equation`, `SliceRecovery`'s `parametric_recovery` /
`parametric_qualitative_stability`, `TuranSliceIdentities`'s
`parametric_recovery_identities` (inherited via `parametric_recovery`),
`GraphonKernelTransport`'s `k4freeP4_graphon_Rtau_eq_zero` / `k4freeP4_graphon_Reta_eq_zero` /
`k4freeP4_graphon_tripartite` (inherited via the `k4freeP4_*` slice equations they consume),
`GraphonRepresentation`'s `k4free_p4_tripartite_of_represents` / `k4free_p4_tripartite_of_rep_exists`
(inherited via `k4freeP4_graphon_tripartite`), `GraphonParametricTransport`'s
`parametricP4_graphon_Rtau_eq_zero` / `_Reta_eq_zero` / `_RtauMinus_le` / `_RtauMinus_eq_zero` /
`_top_endpoint_rigidity` / `parametricP4_top_endpoint_of_represents` / `_of_rep_exists` (inherited via
the general-`r` slice equations, and via `parametricP4_sq_bounds`), and
`ParametricStabilityModulus`'s `parametric_stability_via_modulus` /
`parametric_graphon_stability_via_modulus` (inherited via `parametricP4_K4_density_approx`) —
additionally depend on

```
[Lean.ofReduceBool, Lean.trustCompiler]
```

The reason: the `Automation` layer proves its flag-enumeration bridges by `native_decide`, so any
consumer of the certificate inherits **compiled-evaluation trust** — for these theorems the Lean
*compiler* (not just the kernel) joins the trusted base. `MetaTheory` itself contains **no**
`native_decide`; the inheritance is the whole story.

Crucially, the `Automation` layer's two *declared* axioms — `Zykov_K4_density_bound` and
`Turan_limit_P4_density` — are provably **not** used by any `MetaTheory` theorem (verified by
`#print axioms`): the Zykov bound enters only as the explicit hypothesis `hZykov` (its equality
case as `hZykEq`), and axiom-backed slice-nonemptiness enters only as `hne` hypotheses
(Deviation 14a). So no mathematical statement is postulated anywhere in the `MetaTheory`
dependency cone; the Tier-2 increment over Tier 1 is purely the compiled-evaluation trust of
`native_decide`.

### How to verify it yourself

```bash
# from the repository root
lake exe cache get                              # fetch the Mathlib cache (don't compile from source)
lake build LeanFlagAlgebras.MetaTheory          # build every MetaTheory module

# confirm there are no incomplete proofs
rg -n '\b(sorry|admit|native_decide)\b' LeanFlagAlgebras/MetaTheory -g '*.lean'   # → no output

# confirm the capstone depends only on the standard axioms (no sorryAx)
echo 'import LeanFlagAlgebras.MetaTheory.CloneClosed
open FlagAlgebras.MetaTheory
#print axioms clone_root_plantable' > /tmp/chk.lean
lake env lean /tmp/chk.lean
# → 'clone_root_plantable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Notable deviations from the paper

The formalisation is faithful to the paper's *statements and arguments*, with a few deliberate,
clearly-bounded changes. (Per-module detail is in [`ARCHITECTURE.md`](./ARCHITECTURE.md).)

**None of these is a *statement* deviation.** Every formalised `theorem`/`def` faithfully encodes the
paper result it claims — that is exactly what the
[statement-level audit](#auditing-the-correspondence-to-papertex) checks, and what makes the
machine-checked, `sorry`-free proofs meaningful. The deviations below are all of three harmless
kinds:

* **Proof route** — a different but equivalent argument reaching the *same* statement. The
  substantive ones: the uniform-clone exact-count planted estimate instead of the paper's
  total-variation bound (Deviation 1); the elementary cherry-count `C₄` edge bound instead of the
  convexity bound (Deviation 9d); **`lem:complementation` (Lemma 50) is
  proved via the complement *homeomorphism* of homomorphism spaces, never constructing the paper's
  flag-algebra complement *isomorphism* `C_σ`** (Deviation 9b); and — for §9.4's `thm:no-interior` —
  a **second-moment (variance/Chebyshev) concentration** in place of the paper's **McDiarmid**
  bounded-difference inequality (absent from Mathlib), reaching the same theorem McDiarmid-free
  (Deviation 10); and — for the §11.5 Turán slice identities — the **transitivity→Dirac route**
  in place of the paper's graphon computation at `T_r` (Deviation 15a).
* **Scope** — a paper result formalised only in part: the abstract `cor:degenerate-family` criterion
  without its named extremal-bound instances (Deviation 9c), the positive half of
  `cor:cluster-graphs` (Deviation 7), and the §11.4–§11.8 classical inputs as named hypotheses
  (Deviation 14) — every §11 result-table row is formalised outright; the only genuine
  partial-coverage item left is `cor:degenerate-family` above.
* **Packaging / minor generalisation** — structural repackaging and statements proved slightly more
  generally than needed (Deviations 4, 6).

Each is detailed below and in the relevant module's header.

1. **Uniform clone sizes in the planted estimate (a simplification).** The paper's
   `lem:planted-estimate` allows arbitrary clone sizes and pays a total-variation error term,
   giving an asymptotic bound `C_m(λ + 1/(n−k) + err_N)`. Our `planted_estimate` restricts to the
   **uniform non-root clone case**, which makes the clone-weighted sampling distribution *exactly*
   uniform and replaces the TV analysis with an **exact binomial good/bad count split**, yielding
   the clean bound `1 − ρ` with `ρ = M^{ℓ−k}·C(n−k,ℓ−k)/C(N−k,ℓ−k)`. This is the route actually
   taken by the capstone (`CloneClosed` drives `1 − ρ → 0` via the two limits in
   [`BinomialRatio`](./BinomialRatio.lean)). It is sufficient because
   `thm:clone-root-plantable` is free to *choose* the clone-size vector.
   *Consequence:* [`ProductTV`](./ProductTV.lean) — which correctly formalises the paper's
   general-clone TV bound `eq:good-unnormalized-weight-bound` — is **superseded and unused** on the
   critical path. It is retained (and marked as such in its header) as a correct, reusable lemma.

2. **The constrained representation theorem is a genuine strengthening.** The paper invokes "the
   representation theorem in the constrained class". Mathlib/this development only had the
   *unconstrained* representation theorem (`positiveHom_as_flagSeq_limit`). We therefore prove a
   new, stronger statement — [`exists_constrained_flagSeq_limit`](./ConstrainedRep.lean) — whose
   approximating flags are themselves **forbidden-free**, by intersecting the (full-measure)
   convergence event with a (full-measure) forbidden-free event under the same `flagSeqMeasure`.

3. **Weak convergence lives on `FlagDensitySpace σ`, not `PositiveHomSpace σ`.** A finite flag's
   density profile is *not* an honest positive homomorphism (it is only approximately
   multiplicative), so the per-term rooting measures cannot be pushed onto `X_σ = PositiveHomSpace σ`.
   [`WeakConvergence`](./WeakConvergence.lean) instead states convergence on the ambient compact
   space `FlagDensitySpace σ` to the inclusion-pushforward `(ℙ[φ₀]).map Subtype.val` — the honest
   object, still usable with a Portmanteau argument on `X_σ`.

4. **Minor generalisations / packaging.** `lem:support-as` is stated for any hereditarily-Lindelöf
   space (compact metric spaces qualify); `forbiddenIdeal_eq_span` concludes an equality of
   *carrier sets* (the ideal and the ℝ-span live in different `SetLike` types) and takes heredity
   as an explicit hypothesis; the hereditary clone-closed class is packaged as a reusable
   `GraphClass` structure ([`GraphClassConstraint`](./GraphClassConstraint.lean)). The
   `lem:planted-mass` count is over `ℚ`. The §9 abstract obstruction theorems — `pinning_obstruction`
   ([`Pinning`](./Pinning.lean), `thm:pinning`) and the endpoint witnesses
   `edgeDegenerate_not_rootPlantable_of_witness` / `coEdgeDegenerate_not_rootPlantable_of_witness`
   ([`EdgeObstruction`](./EdgeObstruction.lean)) — are stated for a general flag-algebra element
   `g : A^σ` and real constant `c`, slightly more general than (hence implying) the paper's `σ`-flag
   `g` with `c ∈ [0,1]`.

5. **§6–§7 are unified through one generalised blow-up** (matching the paper's revised §7, where
   `lem:general-planting-estimate` states the estimate for arbitrary interiors). We define a single
   construction `subBlowup G W` (the within-class family `W` is `⊤` for §6 and the in-class fibres
   for §7) and prove the estimate **once**: `planted_estimate_sub` is the §5 `planted_estimate`
   generalised to an arbitrary host (`planted_estimate_host`), since on the transversals the estimate
   samples, `subBlowup` is indistinguishable from the independent blow-up.
   Consequently the §6/§7 estimates inherit the uniform-clone simplification of Deviation 1 (the
   clean `1 − ρ`, with the same `ρ`), not the paper's general-clone `C_m(λ + 1/(n−k) + err_N)`.
   Likewise `subst_root_plantable` is `clone_root_plantable` re-run over `subBlowup` under an abstract
   *within-class blow-up closure* hypothesis, of which §6's `TrueCloneClosed` and §7's
   `SubstitutionClosed` are instances.

6. **§6–§7 packaging.** Heredity is separated from closure into a `HeredClass` structure
   ([`HeredClass`](./HeredClass.lean)), with the §5 `GraphClass extends HeredClass` adding
   `clone_closed` — because `cor:cluster-graphs` needs a class that is hereditary yet *not*
   clone-closed. The closure-agnostic constraint/consumption machinery and the construction-agnostic
   capstone toolkit ([`CapstoneShared`](./CapstoneShared.lean)) are therefore shared by §5, §6 and §7
   rather than duplicated. §7's "infinite" hypothesis is stated as its used consequence — the class
   contains a graph of every finite order (`∀ N, ∃ H : SimpleGraph (Fin N), hc.Mem H`). Cluster
   graphs are encoded by the equivalent `P₃`-free condition "adjacency is transitive on distinct
   vertices" rather than literally "disjoint union of cliques".

7. **`cor:cluster-graphs`: only the positive half is formalised.** We prove cluster graphs are
   root-plantable (`cluster_root_plantable`). The paper's accompanying remark that the class is *not*
   clone-closed (witnessed by `K₂`'s independent blow-up `K_{2,2} ⊇` induced `P₃`) is a separate
   finite construction we did not formalise; it is not needed for any theorem.

8. **§8 deviations.** The §8 *statements* are formalised faithfully; the deliberate changes are:
   * **(a) `thm:sparse-repair-planting` avoids the probabilistic coupling — a genuine simplification.**
     The paper proves the sampling estimate by *coupling* two without-replacement samples drawn from
     different ground sets (`|W| = N − k` for `H`, `|U| = n − k` for `G`) on one probability space.
     We instead prove a **purely combinatorial three-term bound** `counting_coupling_bound` (in
     [`SparseRootRepair`](./SparseRootRepair.lean)):
     `|p_H − p_G| ≤ 2·P_W[S⊄U] + P_W[S⊆U ∧ Bad]`, where the `C(N−k,q)` vs `C(n−k,q)` denominator
     mismatch (the very thing the coupling reconciles) is absorbed by elementary `Finset.card`
     algebra over `Finset.powersetCard`. No PMF/joint-distribution/measure-coupling machinery is
     introduced. The two bad-event bounds are binomial superset counts (the `C(|W|−1,q−1)`/
     `C(|W|−2,q−2)` ratios, via the same superset-count idiom as `PlantedEstimate`). The constant is
     `2mkλ + 4m²ρ` (a factor-2 looser on the first term than the paper's `2mkλ`), harmlessly absorbed
     since the theorem only needs *some* `λ, ρ` making the bound `< ε`.
   * **(b) "Non-degenerate type" is `0 < n₀`.** `thm:finite-local-planting` takes `hn₀ : 0 < n₀`. The
     two `C₅` instances are the one-vertex type `oneVertexType := (⊥ : SimpleGraph (Fin 1))` (`n₀ = 1`)
     and the two-root non-edge type `twoNonEdgeType := (⊥ : SimpleGraph (Fin 2))` (`n₀ = 2`).
   * **(c) Construction presentation.** `oneRootPlant`/`twoRootPlant` are built on the sum type
     `nonRoot G ⊕ (Fin k × Fin L)` (matching the paper's `U ⊔ R₁ ⊔ ⋯ ⊔ R_k`); since
     `FinitePlanting`'s conclusion asks for `H : SimpleGraph (Fin N)`,
     `sparseRootRepair_finitePlanting` transports the sum-type graph onto `Fin N` via
     `Fintype.equivFin` (`SimpleGraph.map`/`Iso.map`), and computes densities on the sum type via the
     iso-invariance `flagDensity₁_respect_eqv`. Clause (iii) of `def:sparse-root-repair` is encoded as
     a `Sym2`-symmetric-difference cardinality bound.
   * **(d) `twoRootPlant_c5free` is slightly more general than the paper lemma.** It is stated with
     the non-edge hypothesis `hrs : ¬ G.Adj r s` (to mirror `def:c5-nonedge-planting`), but the
     projection-based `C₅`-freeness proof does not use it; the non-edge property is supplied to the
     sparse-repair *instance* automatically from the type being `⊥`.

9. **§9 deviations.** The §9 / §9.1 / §9.2 *statements* are formalised faithfully; the deliberate
   choices are:
   * **(a) `cor:codegenerate` (Cor 51) is proved *without* `lem:complementation` (Lemma 50).** The
     paper proves Cor 51 by transferring `thm:degenerate-obstruction` for `K̄` back to `K` through the
     complementation isomorphism `lem:complementation`, and *separately* "identifies the witness
     directly". We take **only the direct-witness route**: `coDegenerate_not_rootPlantable` is built
     from the `c = 1` endpoint of `pinning_obstruction` (via `ae_e_eq_one_of_pinned`, i.e. a
     `[0,1]`-valued mean-`1` variable is a.s. `1`) plus a co-star quotient point with `ψ(e) = 0` — it
     contains **no graph-complement reasoning at all**. This matches the paper's own "Let us also
     identify the witness directly" argument and makes Cor 51 independent of Lemma 50.
   * **(b) `lem:complementation` (Lemma 50) is formalised via the homeomorphism route, not the
     paper's algebra-isomorphism route.** The paper builds the explicit graph-complement *algebra
     isomorphism* `C_σ : A^σ[T] ≅ A^{σ̄}[T̄]` and transports `Q_σ`, `S_σ` and the random-extension
     measures through it. We instead build the complement **homeomorphism** of homomorphism spaces
     directly — `complHom : PositiveHom σ → PositiveHom σᶜ` (the complemented homomorphism, built from
     its density profile via `positiveHomFromZeroSpaceOneMulProp`, the three homomorphism axioms
     transferred through the density identities `flagDensity Fᶜ Gᶜ = flagDensity F G`), packaged as
     `complHomeo : PositiveHomSpace σ ≃ₜ PositiveHomSpace σᶜ` — and never construct the flag-algebra
     algebra isomorphism. The capstone `complementation_invariance`
     ([`ComplementInvariance`](./ComplementInvariance.lean)) — `RootPlantable (K.constraintOf σ) ↔
     RootPlantable (K̄.constraintOf σᶜ)` — then follows from `complHomeo '' Q_σ(K) = Q_{σᶜ}(K̄)`, the
     measure pushforward `Φ_* ℙ[φ₀] = ℙ[φ̄₀]` (via `measure_eq_of_integral_flag_eq`), and
     `complHomeo '' S_σ(K) = S_{σᶜ}(K̄)`. Same theorem; a leaner proof route. (The four-module stack
     `FlagComplement`/`ComplementHom`/`ComplementClass`/`ComplementInvariance`.) Independently, the
     *concrete* dense instance of (a), `coC4free_not_rootPlantable` ([`DenseObstruction`](./DenseObstruction.lean)),
     still uses complementation only **elementarily** — the edge-count identity `e(G) + e(Gᶜ) = C(|G|,2)`
     (`card_edgeFinset_add_compl`) and the graph equality `(coStarₙ)ᶜ = starₙ` — never even the
     homeomorphism, which is why Cor 51 there is genuinely Lemma-50-independent.
   * **(c) `cor:degenerate-family` (Cor 49): the general criterion, not all four families.** We
     formalise the common mechanism `edgeDegenerate_of_subquadratic` ([`DegenerateFamily`](./DegenerateFamily.lean)):
     a subquadratic edge bound `e(G) ≤ f(|G|)` with `f N / N² → 0` implies edge-degeneracy. Only the
     `C₄ = K_{2,2}` instance has its extremal bound proved from scratch (`c4free_card_edges_sq_le`);
     the other listed families — general `K_{s,t}` for `s ≥ 3` (Kővári–Sós–Turán), even cycles
     (Bondy–Simonovits), planar graphs (Euler) — instantiate the criterion via classical extremal
     bounds that are outside the current Mathlib, so they are stated at the level of the criterion
     rather than re-proved.
   * **(d) The `C₄` edge bound is an elementary cherry double-count, not the paper's convexity bound.**
     The paper bounds the average degree by `d̄ ≤ 1 + √N` (Jensen/convexity applied to
     `∑_v C(d(v),2) ≤ C(N,2)`). We instead prove the equivalent-strength `(2·e(G))² ≤ 2N³`
     (`c4free_card_edges_sq_le`) by double-counting cherries
     `∑_v d(v)(d(v)−1) = ∑_{x≠y} |N(x) ∩ N(y)| ≤ N(N−1)` (each pair has ≤ 1 common neighbour, else a
     `C₄`) followed by Cauchy–Schwarz, and then squeeze the **squared** density
     `(e(G)/C(N,2))² ≤ 2N/(N−1)² → 0` — working with the square avoids introducing `√`. Same
     conclusion (edge density → 0), a different elementary route.
   * **(e) The edge flag and `def:edge-degenerate`.** `EdgeDegenerate` is `φ₀(ρ) = 0` for all
     `φ₀ ∈ Q₀`, with `ρ := ⟦e⟧₀` and `e` the one-root edge over `vtype := (⊥ : FlagType (Fin 1))`. The
     unlabelling weight `downwardNormalizingFactor edgeFF.2 = 1` (`downwardNormalizingFactor_edge_eq_one`,
     proved via `isomorphismCount edgeLabeled = 2` — the edge `K₂` has two root placements, flag-iso
     via the `0↔1` swap) makes `φ₀(ρ)` the *genuine* unlabelled edge density, matching the paper's `ρ`
     and `⟨e⟩_v = ρ`. The "contains arbitrarily large stars" hypothesis (weakenable per the paper's
     remark) is encoded as `∀ N, ∃ n ≥ N, hc.Mem (starLabeled n).graph`.
   * **(f) `c4FreeClass` uses Mathlib `Free`/`IsContained`.** `Mem G := (cycleGraph 4).Free G` (no `C₄`
     as a not-necessarily-induced subgraph) — the same direct subgraph-containment encoding as §8's
     `c5FreeClass`, equal to the paper's `K_{C4}` (which it also describes in induced-flag language as
     forbidding the three four-vertex graphs containing a `C₄`).

10. **§9.4 deviations (`thm:no-interior`, `subsec:boundary`).** The §9.4 *statement*
    (`no_interior_pinning`) is formalised faithfully; the deliberate choices are:
    * **(a) McDiarmid-free concentration — a proof-route deviation.** The paper realises a
      deterministic in-class thinned subgraph tracking the expected induced densities by applying
      **McDiarmid's bounded-difference inequality** to the random edge-thinning. Mathlib has no
      McDiarmid / bounded-difference inequality, so `exists_thinned_realization`
      ([`EdgeThinning`](./EdgeThinning.lean)) instead uses a **second-moment (variance/Chebyshev)**
      concentration plus a union bound. The variance bound rests on a **block-independence** lemma —
      the indicators `1_S` and `1_{S'}` of two `k`-subsets sharing `≤ 1` vertex are independent under
      the product Bernoulli measure (`Measure.pi` coordinate independence over `Sym2 (Fin N)`) — same
      theorem, McDiarmid-free.
    * **(b) The first-moment bound is the *correct induced-density* form, not the naive `λ^{e(M)}`.**
      `thinExpectDensity_le_pow` ([`EdgeThinning`](./EdgeThinning.lean)) bounds the expected induced
      density of `M` by `C(C(|M|,2), e(M))·λ^{e(M)}`, **not** `λ^{e(M)}` — the naive bound is *false*
      for induced densities (e.g. an induced `P₃` in a thinned `Kₙ` has density `3λ²(1−λ) > λ²`). The
      binomial constant `C(C(|M|,2), e(M))` is **λ-independent**, so it does not affect the `λ → 0`
      argument; the σ-type lower bound `thinExpectDensity_type_ge` supplies the matching `≥ λ^{e(σ)}`.
    * **(c) The boolean point is the explicit "edgeless cloud" `σ ⊎ K̄_m` limit.** The `{0,1}`-valued
      profile `ψ_σ` is built as the limit of the edgeless-cloud flags and placed in `S_σ`
      (`exists_boolean_point_in_Sσ`, [`NoInteriorThinning`](./NoInteriorThinning.lean)) by an
      **L¹/Markov cylinder argument** over the thinned moments as `λ → 0`.

11. **§9.5 deviations (`thm:c5-edge-not-root-plantable`, `sec:c5-edge`).** The §9.5 development is
    faithful (no statement deviation): `lem:c5-few-triangles` (`c5free_three_mul_triangle_le`) is the
    paper's `3T ≤ 2e`, proved via the double-count `3·T(G) = ∑_v e(G[N(v)])`
    (`three_mul_card_cliqueFinset_three_eq`) together with §8's `lem:c5-nbhd`; the triangle-density-→-0
    squeeze (`c5FreeClass_triangleDensity_zero`) mirrors §9.1's edge-density case; and the
    book-graph's `C₅`-freeness (`book_c5free`) and `F_△`-density `1` (`book_Ftri_density`) are direct.
    The quotient-point assembly is the generic `exists_Qσ_point_flag_eq` (any `σ`, any flag).

12. **§10 formalisation choices (`EmptyTypeCollapse`/`CertificateCones`/`VanishingIdeal`/`SinglePoint`).**
    * **(a) `Q₀`-seminorm closures are stated in ε-form.** The paper takes closures of the
      certificate cones in the seminorm `‖u‖_{Q₀} = sup_{φ₀∈Q₀}|φ₀ u|`. The Lean statements
      (`Q0Within`, `MemQ0Closure`) express `‖u−v‖_{Q₀} ≤ ε` pointwise (`∀ φ₀ ∈ Q₀,
      |φ₀ u − φ₀ v| ≤ ε`) and closure membership as ε-approximability — the same content,
      without formalising a seminormed space.
    * **(b) Ambient sums of squares.** `quotCone` uses sums of squares of the *ambient* algebra
      `A^σ[T₀]` (Mathlib's `IsSumSq`), whereas the paper's cone uses sums of squares of the
      quotient `A^σ[T₁]`. The ambient cone is contained in the paper's cone (apply `qmap`), which
      is contained in `ensCone` (a quotient positive hom evaluates a square non-negatively), so
      the proved closure equality — with the *smallest* of the three cones — implies the paper's.
      (The sandwich argument itself uses two standard §2–§3 facts — surjectivity of the quotient
      map and compatibility of unlabelling with the quotient — that are asserted in the paper and
      not separately formalised; they justify this documentation note only, no Lean statement or
      proof depends on them.)
    * **(c) Evaluation form of "zero in `A⁰[T₁]`".** `prop:ideal-zero` and `prop:single-point`
      conclude that certain unlabelled averages are the zero element of `A⁰[T₁]` (resp. a
      non-negative multiple of the unit). The Lean statements assert the evaluation form — the
      value at **every** `φ₀ ∈ Q₀` is `0` (resp. `c`) — which is exactly what the paper's proofs
      establish and what all uses consume; equality in the quotient algebra itself would
      additionally require a separation theorem for `A⁰[T₁]` that is not part of this development.
    * **(d) `thm:no-closed-certificate-gap` holds without non-degeneracy.** The paper assumes `σ`
      non-degenerate; the Lean proof needs no such hypothesis — at a degenerate base point every
      unlabelled average vanishes (`downward_eval_eq_zero_of_degenerate`), so such points never
      distinguish the cones.
    * **(e) Direct mirror for the co-degenerate case.** The paper derives the co-edge-degenerate
      half of `prop:single-point` by complementation (`lem:complementation`); the Lean proof
      mirrors the edge-degenerate argument directly (complete flags in place of edgeless flags),
      which is shorter than transporting the cone identity through `complHomeo`.
    * **(f) Non-vacuousness in `prop:single-point`.** The literal identity
      `S_vtype = {edgelessPoint}` takes the explicit hypothesis that some constrained limit
      exists (`hne`), which the paper leaves implicit; the cone-collapse statements avoid it
      (when `Q₀ = ∅` the evaluation claim is vacuous and `c = 0` works).

13. **§11.2–§11.3 formalisation choices (`RelativeSupport`/`RelativeClosure`/`RelativeSlackness`/
    `KernelSlackness`).** The relative-theory *statements* are formalised faithfully; the
    deliberate choices are:
    * **(a) `Y` is an arbitrary subset of `X₀`.** The paper fixes a *nonempty* `Y ⊆ Q₀`; no
      §11.2–§11.3 statement needs either hypothesis (an inadmissible or degenerate base limit
      contributes nothing to `S_σ(Y)`, and `downward_eval_eq_zero_of_degenerate` handles
      `φ₀(⟨σ⟩) = 0`), so the Lean statements quantify over any
      `Y : Set (PositiveHomSpace ∅ₜ)` — a strict generalisation; the paper's setting is the
      special case, and `Sσ_eq_relSσ` (with `Y = Qσ forb0`) recovers the absolute theory
      *definitionally* (`rfl`).
    * **(b) Squared form of the `√Δ` first-moment bounds.** `cor:sos-first-moments` is stated as
      `(φ₀ ⟦l·g⟧₀)² ≤ (Δ/λᵢ)·φ₀ ⟦g·g⟧₀` (and `(φ₀ ⟦l⟧₀)² ≤ Δ/λᵢ`), avoiding `Real.sqrt`; the
      paper's form follows by taking square roots.
    * **(c) `prop:unique-slice-stability` for an arbitrary index family.** The paper takes
      countably many density equations; the proof is pure compactness, so the Lean statement
      allows any index type `J`.
    * **(d) Cauchy–Schwarz by reuse.** `lem:relative-cauchy-schwarz` is a thin wrapper over the
      pre-existing base-library lemma `square_downward_mul_ge_mul_downward_square`
      (`FlagAlgebra/RandomHom.lean`) — the identical inequality, already proved there through the
      extension measure, exactly as the paper remarks ("Razborov's Cauchy–Schwarz, re-proved
      through the extension measure").
    * **(e) `thm:kernel-slackness` via the existing `flagQuadraticForm`.** The paper's
      `⟨Q v, v⟩` is the base library's `flagQuadraticForm Q v`
      (`FlagAlgebra/QuadraticForm.lean`), so the kernel form plugs into the SOS machinery already
      used by the repository's certificate developments; the row combination `wᵀQv` is
      `kernelCombo Q v w = ∑ₐ (Q *ᵥ w)ₐ • vₐ` (equal to the paper's by symmetry of `Q`). The
      closing sentence of conclusion (4) — that a basis of the row space yields
      `rank Q` linearly independent equations — is elementary linear-algebra prose and is not
      separately formalised; the Lean conclusion `Q *ᵥ χ(v) = 0` *is* the full list of row
      equations.
    * **(f) Remarks are mostly not formalised.** `rem:quotient-elements` (transfer between
      `f ∈ A^σ[T₀]` and its quotient image), `rem:kernel-practice`, and the two unnamed remarks
      are expository; the Lean statements are phrased directly in the ambient algebra `A^σ[T₀]`,
      which is the formulation the remarks justify. The one *mathematical* claim inside
      `rem:cs-shape` — for the standard instance `fᵢ = l·l`, the exact/global conclusions read
      `ψ(l) = 0` a.s. / `l = 0` on `S_{σᵢ}(Y)` — **is** exported
      (`relative_slackness_exact_ae_sq` / `relative_slackness_global_sq`).

14. **§11.4–§11.8 formalisation choices (the slice method + the graphon layer).** The applied
    slice results are formalised faithfully — every result-table row for §11 is formalised, modulo
    the four permanent classical inputs — see [Scope &
    limitations](#scope--limitations); the deliberate choices are:
    * **(a) Classical inputs are named hypotheses, not axioms.** Erdős–Simonovits uniqueness of
      the extremal Turán/Mantel limits enters as `hpin` (`mantel_not_relatively_plantable`; `hpin`
      is also itself a theorem under the §11.5 identities' ES hypothesis `hES` — Deviation 15) and
      `huniq` (`k4free_qualitative_stability`); Zykov's `K₄`-density bound as `hZykov` and its
      equality case as `hZykEq` (`ParametricP4Slice`/`SliceRecovery`); stability moduli as `hmod`
      (`Graphon.stability_via_modulus`); and slice nonemptiness, where it is axiom-backed upstream
      (the `Automation` layer's `Turan_limit_P4_density`), as `hne` hypotheses. No classical
      statement is postulated anywhere in `MetaTheory`.
    * **(b) The §11.7–§11.8 graphon layer is self-contained kernel measure theory on
      `unitInterval`.** Mathlib has no graphons — [`GraphonBasic`](./GraphonBasic.lean) defines
      them from scratch. The layer connects to the flag/hom layer only through the paper's
      flag↔kernel dictionary, which is part of the unformalised Lovász–Szegedy representation —
      so the kernel theorems take the certificate-supplied `R`-bounds as hypotheses rather than
      deriving them from the hom-level certificate.
    * **(c) Rigidity is concluded in measurable-partition form.** `Graphon.slice_rigidity`
      produces a measurable `P : I → Fin r` with all fibers of volume `1/r` and `W = 0`/`1` by
      block a.e., rather than the paper's "up to measure-preserving relabelling, `T_r`"; the
      final relabelling is a cosmetic step not formalised.
    * **(d) Squared / abstracted quantitative forms.** The `√Δ` bounds are kept in squared form
      (as in Deviation 13b) and the `Δ^{1/4}` rates as nested square roots; the modulus
      implications are abstracted over the target predicate (`close` in
      `Graphon.stability_via_modulus`), with the cut-distance modulus `δ□` itself not formalised.
    * **(e) Tier-2 axiom inheritance.** The certificate consumers carry
      `[Lean.ofReduceBool, Lean.trustCompiler]` on top of the standard three — see
      [Axioms assumed](#axioms-assumed).
    * **(f) The certificate's `p₀·f₀ + leftover` is folded into the slackness slack term `n`.**
      `gap_identity`'s non-square remainder enters `relative_slackness_*` through its slack
      element `n`, so the mined slice equations come out exactly as in the paper without
      re-deriving the certificate's shape inside `MetaTheory`.
    * **(g) The Mantel witness graph is parity-bipartite `K_{n+1,n+1} + w`.** The paper's witness
      is `K_{n,n}` plus an isolated root; `knnPlusW` bipartitions the first `2(n+1)` vertices by
      parity and isolates the last — the same limit, a cleaner `Fin` indexing.

15. **§11.5 Turán slice identities (`TuranAut`/`TuranDirac`/`TuranSliceIdentities`).** The
    identity halves of `thm:turan-slice`/`thm:relative-mantel` and the Cor 105 "consequently"
    clauses are formalised faithfully; the deliberate choices are:
    * **(a) The transitivity→Dirac proof route — no graphons, no second moments.** The paper reads
      the pinned rooted densities off the graphon `T_r`. The Lean route avoids graphons **and**
      second-moment computations entirely: **Turán graphs are vertex- and ordered-pair transitive**
      (`turan_vertex_transitive` / `turan_pair_transitive`, [`TuranAut`](./TuranAut.lean)), so all
      `σ`-labellings of a Turán flag are a single flag class
      (`labelExtensions_turan_{vtype,edge,nonEdge}_subsingleton`), **every finite rooting measure
      is exactly Dirac** (`toProbMeasure_eq_dirac_of_subsingleton`), and Dirac-ness passes to the
      weak limit — Mathlib's `diracProba` is a closed embedding on the compact metric profile
      space (`extend_eq_dirac_of_labelExtensions_subsingleton`,
      [`TuranDirac`](./TuranDirac.lean)). The pinned values are then plain **single-root extension
      counts** in `turanGraph (r·m) r`. Same statements, an elementary route.
    * **(b) The Erdős–Simonovits singleton claim is the named hypothesis `hES`.** It enters as
      `hES : turanSlice r ⊆ {posHomPoint (turanLimit r hr)}` — **equivalent** to the paper's
      "consists of exactly one point", since `turanLimit_mem_slice` supplies the reverse inclusion
      unconditionally. Only ES itself remains classical input (as in Deviation 14a).
    * **(c) `parametric_recovery_identities` assumes `3 ≤ r` where the paper says `r ≥ 4`.** A
      hypothesis weakening/generalisation: at `r = 3` the `hZykEq` input degenerates, but the
      statement stays sound as a conditional.
    * **(d) The identities are stated at the generated types, in the §9 `e`-vocabulary at
      `vtype`.** The `τ`/`η` identities are phrased at the generated flag types
      `FlagType_2_1`/`FlagType_2_0` via the generated-flag dictionary
      (`FlagAlgebra_3_2_1_{1,2,3,0}` ↔ `a_τ, b_τ, g_τ, z_τ`;
      `FlagAlgebra_3_2_0_{0,3,1,2}` ↔ `z_η, g_η, a_η, b_η`); the vertex-type identity uses §9's
      one-root edge flag `e`.

16. **`graphonHom`: every graphon is a positive homomorphism**
    (`GraphonInducedDensity`/`PairSubsetCount`/`EmptyTypeGraphBridge`/`GraphonHom`). There is no
    single `paper.tex` display to formalise here: the paper's §11.7 area cites "every graphon is a
    limit object" as folklore, needed for the (still open) *hom→graphon* direction of the
    Lovász–Szegedy representation. This module formalises the *other* direction, graphon→hom, as
    reusable infrastructure; the deliberate choices:
    * **(a) Subset-averaging, not orbit-stabiliser counting.** The profile `graphonProfileFun`
      sums the induced density `graphonFlagDensity` ([`GraphonInducedDensity.lean`](./GraphonInducedDensity.lean))
      over *every* labelled graph in an isomorphism class, and both structural properties
      (`zeroSpaceProp`/`mulProp`) are proved by averaging that sum over vertex-subset embeddings:
      any two embeddings `Fin n ↪ Fin ℓ` (resp. disjoint pairs of embeddings) are related by a
      permutation of `Fin ℓ` (`exists_perm_comp_emb`/`exists_perm_comp_emb_pair`,
      [`EmptyTypeGraphBridge.lean`](./EmptyTypeGraphBridge.lean)), and both the induced density
      (`graphonFlagDensity_comap_equiv`) and the flag class (`graphFlag_comap_equiv`) are
      permutation-invariant — so the averaging argument never needs to count automorphisms or
      orbit-stabilisers of the target flag class (contrast the transitivity→Dirac route of
      Deviation 15, which collapses a *measure* via automorphisms of one graph; here
      permutation-invariance of a density/class pair collapses an *average* directly).
    * **(b) Minimal new base-bridge machinery.** The pre-existing
      `LabeledCount.flagDensity₁_eq_subset_count_div` is reused as-is, specialised to the empty
      type by `flagDensity₁_graphFlag`; only its **pair** analogue
      ([`PairSubsetCount.lean`](./PairSubsetCount.lean), specialised by `flagDensity₂_graphFlag`)
      is genuinely new, needed because `mulProp` is a two-flag (joint) statement.
    * **(c) `graphonHom_edge` is a deliberate sanity check, not a dependency.** It links the new
      flag-algebra-side profile `φ_W` back to the pre-existing §11.7 kernel layer
      (`GraphonBasic.edgeDensity`) at the one point (the edge) where both sides compute the same
      quantity by construction; nothing downstream currently consumes it.
    * **(d) Infrastructure, not a numbered theorem.** `graphonHom`/`graphonProfile` and its three
      structural lemmas have no `\label` to check against; the statement-level audit here is
      against the module's own informal spec ("the probability that a `W`-random graph on `|F|`
      uniform samples is isomorphic to `F`"), not a paper display.

17. **The rooted transport's slice-membership hypothesis `hmem` is a named hypothesis, not an
    existential representation.** ([`StdRootedBridge`](./StdRootedBridge.lean)/
    [`GraphonRootedDensity`](./GraphonRootedDensity.lean)/[`GraphonRootedHom`](./GraphonRootedHom.lean)/
    [`GraphonRootedMeasure`](./GraphonRootedMeasure.lean)/
    [`GraphonKernelTransport`](./GraphonKernelTransport.lean).) The paper's route to
    `thm:k4free-p4-tripartite` begins "let `W` represent a point of `Y_{P4}`" — i.e. it assumes a
    graphon *already given* as a representative of a slice point. Lean instead takes
    `hmem : posHomPoint (graphonHom W) ∈ k4freeP4Slice` (`φ_W` itself, built from any graphon `W`
    via the now-formalised graphon→hom direction, lies in the slice) together with the two
    root-type admissibility hypotheses `hστ`/`hση` (`(graphonHom W)⟨FlagType_2_1/2_0⟩₀ > 0`) as
    named hypotheses on `k4freeP4_graphon_tripartite`. This is not a strengthening or a weakening —
    `hmem` is purely algebraic (`mem_Qσ_iff`: `φ_W` vanishes on the forbidden `K₄` flags plus the
    `P₄`-density evaluation; no graph-limit existential enters, per the module's design note) — but
    it packages the paper's informal "let `W` represent…" as an explicit predicate on `W` rather
    than an existential quantifier over slice points. Once the still-open hom→graphon direction of
    the Lovász–Szegedy representation theorem is available, composing that existence theorem with
    `k4freeP4_graphon_tripartite` recovers the paper's Thm 102 verbatim (any `φ₀ ∈ k4freeP4Slice`
    has *some* representing `W`, and `hmem` holds for it by construction).

18. **`paper.tex` §11 states its classical inputs explicitly, in the same shape the formalisation
    uses.** A standing paragraph at the head of §11 names the four classical results that enter as
    unproved external inputs (Erdős–Simonovits stability, Zykov's `K₄`-density bound and its
    equality case, and Lovász–Szegedy existence) and fixes the convention that every dependence on
    one is an explicit hypothesis of the result that uses it — mirroring the Lean's `hES`/`hZykov`/
    `hZykEq`/`hrep` hypotheses. This is a *paper*-side alignment fact, not a Lean deviation, recorded
    here because it is what the audit tables above check against. Correspondingly:
    * Thm 91 (`thm:turan-slice`) and Thm 92 (`thm:relative-mantel`) are each split into an
      unconditional *existence* half and an Erdős–Simonovits-*conditional* uniqueness half, with
      the exact ES instance stated as a hypothesis (matching `turanSlice_nonempty`/`hES` here);
    * Prop 86 (`prop:mantel-not-plantable`) names its inherited ES hypothesis in the statement
      rather than letting it enter silently through a citation of Thm 92;
    * Thm 102 (`thm:k4free-p4-tripartite`) is stated with the quantifier over *representing*
      graphons and the two positive-root-mass hypotheses made explicit — matching
      `k4free_p4_tripartite_of_represents` verbatim;
    * Cor 105 (`cor:parametric-p4-turan-recovery`) is stated for `r ≥ 3` rather than `r ≥ 4` (the
      formalisation proves the wider range; at `r = 3` the Zykov hypothesis is redundant by
      `cor:r3-rigidity`);
    * Cor 106 (`cor:top-endpoint-recovery`) is stated in the same representative-quantified
      shape as Thm 102 — matching `parametricP4_top_endpoint_of_represents` verbatim — and for
      `r ≥ 3` rather than `r ≥ 4` in the "consequently" recovery corollary;
    * Thm 97 (`thm:parametric-p4-equality-slice`) states Zykov's `K₄`-density *bound* (the plain
      inequality, not the equality case) as an explicit hypothesis for `r ≥ 4`, matching
      `parametricP4_K4_density`/`parametricP4_eta_equation`'s separate `hZykov` hypothesis (logically
      distinct from `hZykEq`, and used unconditionally for `r ≥ 4` even where the equality case is
      never invoked — the reason the standing paragraph names **four**, not three, classical
      inputs);
    * Thm 112(iv) and Prop 110 need no such alignment: their hypothesis shape (an explicit
      Zykov-equality hypothesis, an assumed modulus `ω_Zyk`) already matches the formalisation
      convention.

None of these changes the theorems being proved; they are formalisation choices, and each is
documented in the relevant module's header.

---

## Auditing the correspondence to `paper.tex`

Because every proof is machine-checked and `sorry`-free, **a human audit reduces to checking that
each Lean *statement* faithfully encodes the corresponding paper claim** — the kernel guarantees the
rest. So the audit is *statement-level*: read the Lean `def`/`theorem` and compare it to the paper
`\begin{definition}`/`\begin{theorem}` it claims to formalise; you do **not** need to read the
proofs to trust the result, only to satisfy yourself that the hypotheses and conclusion match (and
that any deviation is one of the documented, harmless ones above).

*(The tables below identify each result by its **paper-number label** — `Lemma N` / `Theorem N`, as
assigned in `paper.aux` — rather than a `paper.tex` line number, since line numbers drift whenever
the paper is edited. Locate a result by its `\label{…}` or its number.)*

**General orientation.** The notation map (`⟦·⟧`, `⟦·⟧₀`, `∅ₜ`, `⟨σ⟩₀`, `ℙ[φ₀]`, `≃f`, `↪g`,
`flagDensity₁`, `S_σ`, `Q_σ`, `RootPlantable`) is in [`READING_GUIDE.md`](./READING_GUIDE.md), which
also carries the full *paper-result → module → Lean-name* table for §2–§11.8 (incl. `lem:complementation`). Every module opens with a
`/-! # … -/` header naming the `paper.tex` result(s) it formalises; start there. The semantic
objects (`Q_σ`, `S_σ`, `RootPlantable`, `Constraint`, the random extension `ℙ[φ₀]`) are defined in
[`ConstrainedClass`](./ConstrainedClass.lean) / [`SupportClosure`](./SupportClosure.lean) — read
those definitions once and the meaning of every "`S_σ = Q_σ`" conclusion is fixed.

**§8 audit map** (paper label ↦ Lean statement to read):

| `paper.tex` label | Lean statement to read | What to verify |
|---|---|---|
| `def:finite-local-planting` (Def 26) | `FinitePlanting` ([`FinitePlanting.lean`](./FinitePlanting.lean)) | the three clauses (i) `|V H| ≥ |G|`, (ii) `|Θ| ≥ δ|V H|^k`, (iii) bounded-size density match — and the `∀ m,ε ∃ n₁,δ ∀ …` quantifier order |
| `thm:finite-local-planting` (Thm 27) | `finitePlanting_root_plantable` | conclusion is `RootPlantable (hc.constraintOf σ)` i.e. `S_σ = Q_σ`; non-degeneracy is `0 < n₀` |
| `def:sparse-root-repair` (Def 29) | `SparseRootRepair` ([`SparseRootRepair.lean`](./SparseRootRepair.lean)) | the host vertex type `nonRoot G ⊕ (Fin n₀ × Fin L)` ≙ `U ⊔ R₁⊔⋯⊔R_k`; clauses (i)/(ii) cross-adjacency; clause (iii) `Sym2` symmetric-difference count `≤ ρn²`; `L ∈ [λn/2, λn]` |
| `thm:sparse-repair-planting` (Thm 30) | `sparseRootRepair_finitePlanting` | conclusion `FinitePlanting hc σ` (the proof's coupling-free route is Deviation 8a; the *statement* matches the paper) |
| `lem:c5-nbhd` (Lem 32) | `c5free_neighborhood_edge_card_le` ([`C5Free.lean`](./C5Free.lean)) | `(G.induce (G.neighborSet v)).edgeFinset.card ≤ Fintype.card (G.neighborSet v)` ≙ `e(G[N(v)]) ≤ |N(v)|`; and `c5FreeClass` `Mem G := C5g.Free G` ≙ "no `C₅` subgraph" |
| `def:c5-one-root-planting` (Def 33) | `oneRootPlant` ([`C5OneRoot.lean`](./C5OneRoot.lean)) | the `Adj` match: `R` independent, `R`–`U` join = `N(r)`, `U`-edges kept except inside `N(r)` |
| `lem:c5-planting-free` (Lem 34) | `oneRootPlant_c5free` | `C5g.Free (oneRootPlant G L)` from `C5g.Free G.graph` |
| `lem:c5-one-root-sparse-repair` (Lem 35), `thm:c5-one-root` (Thm 36) | `c5FreeClass_sparseRootRepair_oneVertex`, `c5free_one_root_plantable` | the type is `oneVertexType = (⊥ : SimpleGraph (Fin 1))`; conclusion `RootPlantable (c5FreeClass.constraintOf oneVertexType)` ≙ `S₁ = Q₁` |
| `def:c5-nonedge-planting` (Def 38), `lem:c5-nonedge-planting-free` (Lem 39) | `twoRootPlant` ([`C5TwoRootNonEdge.lean`](./C5TwoRootNonEdge.lean)), `twoRootPlant_c5free` | two clusters, no `R`–`S` edges, delete `U`-edges inside `N(r)` **or** `N(s)`; note Deviation 8d (`hrs`) |
| `lem:c5-nonedge-sparse-repair` (Lem 40), `thm:c5-nonedge-root` (Thm 41) | `c5FreeClass_sparseRootRepair_twoNonEdge`, `c5free_two_root_nonedge_plantable` | the type is `twoNonEdgeType = (⊥ : SimpleGraph (Fin 2))` ≙ the non-edge type `η`; conclusion ≙ `S_η = Q_η` |
| `lem:c5-blowup` (Lem 42) | `c5_blowup_free_iff_triangleFree` ([`C5Blowup.lean`](./C5Blowup.lean)) | `(∀ m, C5g.Free (independentBlowup G m)) ↔ G.CliqueFree 3` |

**§9 (§9.1–§9.5) + `lem:complementation` audit map** (paper label ↦ Lean statement to read):

| `paper.tex` (paper #) | Lean statement to read | What to verify |
|---|---|---|
| `thm:pinning` (Thm 53) | `pinning_obstruction` ([`Pinning.lean`](./Pinning.lean)) | almost-sure pinning of `g` to `c` under every admissible extension **plus** a quotient point `ψ ∈ Q_σ` with `ψ g ≠ c` ⟹ `¬ RootPlantable T` (i.e. `S_σ ≠ Q_σ`) |
| `def:edge-degenerate` (Def 43) | `EdgeDegenerate` ([`EdgeObstruction.lean`](./EdgeObstruction.lean)), `CoEdgeDegenerate` | `EdgeDegenerate hc` is `φ₀ ρ = 0` for **all** admissible `φ₀ ∈ Q₀`, with `ρ := ⟦e⟧₀` the *unlabelled* edge density and `e` the one-root edge over `vtype` (Deviation 9e: `downwardNormalizingFactor = 1`); `CoEdgeDegenerate` is the dual `φ₀ ρ = 1` |
| `thm:degenerate-obstruction` (Thm 44) | abstract: `edgeDegenerate_not_rootPlantable_of_witness` (`EdgeObstruction.lean`); concrete: `degenerate_not_rootPlantable` ([`StarWitness.lean`](./StarWitness.lean)) | abstract form takes `EdgeDegenerate hc` + a `Q_vtype` witness with `ψ e ≠ 0`; concrete form replaces the witness hypothesis with "arbitrarily large stars in the class" (`∀ N, ∃ n ≥ N, hc.Mem (starLabeled n).graph`) and builds the witness from a star sequence |
| `lem:c4-edge-zero` (Lem 47) | `c4FreeClass_edgeDegenerate` ([`C4Free.lean`](./C4Free.lean)); bound `c4free_card_edges_sq_le` | the `C₄`-free class is edge-degenerate; the counting heart is `(2·e(G))² ≤ 2|G|³` (the squared-density route, Deviation 9d) |
| `cor:c4-counterexample` (Cor 48) | `c4free_not_rootPlantable` (`C4Free.lean`) | `¬ RootPlantable (c4FreeClass.constraintOf vtype)` — the `C₄`-free class is the explicit degenerate counterexample at the one-vertex type |
| `cor:degenerate-family` (Cor 49) | `edgeDegenerate_of_subquadratic` ([`DegenerateFamily.lean`](./DegenerateFamily.lean)) | this is the **general subquadratic criterion** `e(G) ≤ f(|G|)` with `f N / N² → 0` ⟹ edge-degenerate; only `C₄` is proved from scratch — the other listed families are criterion *instances*, not re-proved (Deviation 9c) |
| `cor:codegenerate` (Cor 51) | abstract: `coEdgeDegenerate_not_rootPlantable_of_witness` (`EdgeObstruction.lean`); concrete: `coDegenerate_not_rootPlantable` (`StarWitness.lean`) + dense `coC4free_not_rootPlantable` ([`DenseObstruction.lean`](./DenseObstruction.lean)) | the dual *dense* obstruction (`c = 1` endpoint); `coC4FreeClass` (`DenseObstruction.lean`) is the dense complement-of-`C₄`-free class; proved Lemma-50-**independently** via the direct co-star witness (Deviation 9a) |
| `lem:complementation` (Lem 50) | `complementation_invariance` ([`ComplementInvariance.lean`](./ComplementInvariance.lean)) | `RootPlantable (K.constraintOf σ) ↔ RootPlantable (K̄.constraintOf σᶜ)`, with `K̄ = HeredClass.compl` ([`ComplementClass.lean`](./ComplementClass.lean); `Mem G := Mem Gᶜ`); the crux is the homeomorphism `complHomeo` ([`ComplementHom.lean`](./ComplementHom.lean)) and the measure pushforward `complHomeo_map_eq` (`ComplementInvariance.lean`) — the homeomorphism route, not the paper's algebra iso (Deviation 9b) |
| `thm:no-interior` (Thm 55) | `no_interior_pinning` ([`NoInteriorThinning.lean`](./NoInteriorThinning.lean)); boolean point `exists_boolean_point_in_Sσ` | for an `EdgeDeletionClosed` class ([`NoInterior.lean`](./NoInterior.lean)), a σ-flag pinned to `c` on `S_σ` has `c ∈ {0,1}`; the `{0,1}`-valued "edgeless cloud" point lies in `S_σ` (placed by the L¹/Markov cylinder argument over the thinned moments, Deviation 10c). The thinning stack feeding it: `exists_thinned_realization` ([`EdgeThinning.lean`](./EdgeThinning.lean) McDiarmid-free — Deviation 10a/b) and `exists_thinned_limit` ([`EdgeThinningLimit.lean`](./EdgeThinningLimit.lean)) |
| `lem:c5-few-triangles` (Lem 58) | `c5free_three_mul_triangle_le` ([`C5FewTriangles.lean`](./C5FewTriangles.lean)) | `3·T(G) ≤ 2·e(G)` for `C₅`-free `G`, via the double-count `three_mul_card_cliqueFinset_three_eq` `3·T(G) = ∑_v e(G[N(v)])` and §8's `lem:c5-nbhd`; the unlabelled-triangle density is `flagDensity_unlabelledTriangle_eq` `= T(G)/C(N,3)`, squeezed to `0` by `c5FreeClass_triangleDensity_zero` |
| `cor:c5-edge-pinned` (Cor 59) | `ae_Ftri_eq_zero_of_pinned` ([`C5EdgeObstruction.lean`](./C5EdgeObstruction.lean)) | the common-neighbour triangle flag `F_△` (`F_tri` / `triangleFF`) over the two-root `edgeType` (`⊤` on `Fin 2`) is a.s. pinned to `0` under random edge-rooting |
| `def:c5-book` / `lem:c5-book` (Def 60 / Lem 61) | `bookLabeled` (`C5EdgeObstruction.lean`), `book_c5free`, `book_Ftri_density` | the book graph is `C₅`-free (`book_c5free`) with `F_△`-density `1` (`book_Ftri_density`); `exists_book_Qτ_point` packages it as the `Q_τ` point of `F_△`-density `1` |
| `thm:c5-edge-not-root-plantable` (Thm 62) | `c5free_edge_not_rootPlantable` (`C5EdgeObstruction.lean`) | the `C₅`-free class is **not** root-plantable at the two-root edge type `τ` — `cor:c5-edge-pinned` pins `F_△` to `0` while the book point of `def:c5-book` realises `F_△ = 1` in `Q_τ`, contradicting `pinning_obstruction` |
| `cor:c5-no-pin` (Cor 57) | `c5free_triOverVtype_zero_on_Qvtype` (`C5EdgeObstruction.lean`), `c5free_edge_not_pinned` | the two no-obstruction-at-the-vertex-type facts: triangle-over-vtype density `0` on `Q_vtype`, and the edge is not pinned (so the obstruction is genuinely *edge-type*-specific) |

**§10 audit map** (paper label ↦ Lean statement to read):

| `paper.tex` (paper #) | Lean statement to read | What to verify |
|---|---|---|
| `prop:empty-type` (Prop 64) | `extend_emptyType_eq_dirac` ([`EmptyTypeCollapse.lean`](./EmptyTypeCollapse.lean)), `Sσ_emptyType_eq`, `emptyType_rootPlantable`, `emptyType_quotient_iff_ensemble` | `Ext_∅(φ₀) = δ_{φ₀}` ≙ `(ℙ[φ₀] : Measure _) = Measure.dirac (posHomPoint φ₀)`; `S_∅ = Q_∅ = Q₀` ≙ `Sσ T = Qσ T.forb0`; "always root-plantable" takes `hforb : ∀ F, T.forbσ F ↔ T.forb0 F` (the two forbidden predicates agree at the empty type — automatic for a hereditary class, `heredClass_emptyType_rootPlantable`) |
| `cor:confined` (Cor 65) | `ensemble_implies_quotient_emptyType` (`EmptyTypeCollapse.lean`) | an `EnsembleNonneg` bound on `A⁰` is `QuotientNonneg` — no bound is ensemble-true but quotient-false |
| `thm:no-closed-certificate-gap` (Thm 66) | `no_closed_certificate_gap` ([`CertificateCones.lean`](./CertificateCones.lean)); cones `quotCone` / `ensCone`; closure `Q0Within` / `MemQ0Closure`; crux `ensCone_subset_closure_quotCone` | the two cones have the same `Q₀`-seminorm closure; the closure is in ε-form (Deviation 12a), the quotient cone uses ambient sums of squares (12b), and the statement holds for every type, without non-degeneracy (12d) |
| `prop:ideal-zero` (Prop 67) | `downward_eval_eq_zero_of_zero_on_Sσ` ([`VanishingIdeal.lean`](./VanishingIdeal.lean)), `downward_mul_eval_eq_zero_of_zero_on_Sσ`, `pinned_witness_downward_eq_zero`, `downward_eval_congr_of_eqOn_Sσ`; final clause `ensCone_eval_eq_quotCone_of_sos_agreement` ([`CertificateCones.lean`](./CertificateCones.lean), end of file) | vanishing on `S_σ` ⟹ zero unlabelled average at every `φ₀ ∈ Q₀` (evaluation form, Deviation 12c); the ideal clause; the pinning witness `(g − c•1)·h`; agreeing on `S_σ` ⟹ equal averages; and the final clause in contrapositive form — a strict exact cone gap requires a Positivstellensatz gap on `S_σ` |
| `prop:single-point` (Prop 68) | `Sσ_eq_singleton_of_edgeDegenerate` ([`SinglePoint.lean`](./SinglePoint.lean)) / `Sσ_eq_singleton_of_coEdgeDegenerate`; cones `edgeDegenerate_cone_collapse` / `coEdgeDegenerate_cone_collapse`, ray `smul_one_mem_quotCone_vtype`; the points `edgelessPoint` / `completePoint` with value lemmas `edgelessPoint_val` / `completePoint_val` ([`BooleanPoint.lean`](./BooleanPoint.lean)) | `S_vtype` is exactly the labelled empty-graph (resp. complete-graph) limit — the boolean profile `1` on the edgeless (resp. complete) flag of each size, `0` elsewhere — given a constrained limit exists (Deviation 12f); every ensemble-cone member equals some `c ≥ 0` on all of `Q₀` and `c•1₀` is a quotient sum-of-squares average (evaluation form 12c; co-case by direct mirror 12e) |
| `cor:c5-edge-closed-inert` (Cor 70) | `c5free_edge_no_closed_certificate_gap` ([`C5EdgeInert.lean`](./C5EdgeInert.lean)), `c5free_Ftri_zero_on_Sσ`, `c5free_Ftri_mul_downward_eq_zero` | the closed-cone equality instantiated at `(c5FreeClass, edgeType)`; the pinned witness `F_△` vanishes on `S_τ` and, with all its flag-multiples, unlabels to zero on `Q₀` |

**§11.2–§11.3 audit map** (paper label ↦ Lean statement to read):

| `paper.tex` (paper #) | Lean statement to read | What to verify |
|---|---|---|
| `S_σ(Y)` display (§11.2) | `relSσ` ([`RelativeSupport.lean`](./RelativeSupport.lean)); recovery `Sσ_eq_relSσ` | the closure of the union of `supp ℙ[φ₀]` over `posHomPoint φ₀ ∈ Y` with `φ₀ ⟨σ⟩₀ > 0`; `Y` is an *arbitrary* subset of `X₀` (Deviation 13a — the paper's nonempty `Y ⊆ Q₀` is the special case); with `Y = Qσ forb0` this is `Sσ` by `rfl` |
| `lem:relative-closure` (Lemma 71) | `relSσ_closure_eq` ([`RelativeClosure.lean`](./RelativeClosure.lean)); ingredients `extend_tendsto`, `support_subset_closure_iUnion_support` | `S_σ(closure Y) = S_σ(Y)`, closure taken in `X₀ = PositiveHomSpace ∅ₜ`; the two ingredients are the paper's two proof steps (weak continuity of `Ext_σ` where `φ(⟨σ⟩) > 0`; support lower-semicontinuity along weak convergence), stated for sequences — sufficient since `X₀` is compact metrizable |
| `prop:relative-soundness` (Prop 72) | `relative_soundness` ([`RelativeSupport.lean`](./RelativeSupport.lean)) | `f ≥ 0` on `S_σ(Y)` ⟹ `φ₀ ⟦f⟧₀ ≥ 0` for every `φ₀` with `posHomPoint φ₀ ∈ Y` — including the degenerate case `φ₀(⟨σ⟩) = 0` (handled by `downward_eval_eq_zero_of_degenerate`, as in the paper's monotonicity aside) |
| `prop:relative-criterion` (Prop 74) | `relative_criterion` ([`RelativeSupport.lean`](./RelativeSupport.lean)); condition (b) is `RelEnsembleNonneg` | the equivalence holds for every `Y` with **no root-plantability hypothesis** (both directions are the "easy" directions of `thm:support-criterion`); (b) is the paper's `P[ψ(f) ≥ 0] = 1` for every admissible `φ₀ ∈ Y` |
| `thm:relative-slackness` (Thm 76) + `rem:cs-shape` (Rem 77) square instances | `relative_slackness_soundness` / `_approx` / `_term` / `_slack` / `_exact_slack` / `_exact_term` / `_exact_ae` / `_global`, and `_exact_ae_sq` / `_global_sq` ([`RelativeSlackness.lean`](./RelativeSlackness.lean)) | hypotheses (i)–(iii) are `hf`/`hn`/`hcert` with `λᵢ > 0` (`hlam`); conclusions (1)–(4) split across the eight statements — check the a.s. clause of (3) carries the paper's proviso `φ₀(⟨σᵢ⟩) > 0` (`hσi`) and that (4) concludes vanishing *identically on* `S_{σᵢ}(Y)`; the `_sq` forms are `rem:cs-shape`'s standard-instance readings (`fᵢ = l·l` ⟹ `ψ(l) = 0` a.s. / `l = 0` on the support) |
| `lem:relative-cauchy-schwarz` (Lemma 78) | `downward_cauchy_schwarz` ([`RelativeSlackness.lean`](./RelativeSlackness.lean); helper `downward_sq_eval_nonneg`) | `(φ₀ ⟦l·g⟧₀)² ≤ φ₀ ⟦l·l⟧₀ · φ₀ ⟦g·g⟧₀` for **every** `φ₀ ∈ X₀` (no constraint set involved); a wrapper over the base library's `square_downward_mul_ge_mul_downward_square` (Deviation 13d) |
| `cor:sos-first-moments` (Cor 79) | `certificate_first_moment_sq_bound` ([`RelativeSlackness.lean`](./RelativeSlackness.lean)), `_one` | the squared form of the `√Δ` bounds (Deviation 13b): `(φ₀ ⟦l·g⟧₀)² ≤ (Δ/λᵢ)·φ₀ ⟦g·g⟧₀` under `fᵢ = l·l`, and `(φ₀ ⟦l⟧₀)² ≤ Δ/λᵢ` at `g = 1` (the intermediate `φ₀(⟨σᵢ⟩) ≤ 1` step is `posHom_one_downward_le_one`) |
| `thm:kernel-slackness` (Thm 80) | `kernel_slackness_soundness` / `_approx` / `_exact_slack` / `_exact_ae` / `_global` ([`KernelSlackness.lean`](./KernelSlackness.lean)); `⟨Qv,v⟩` is `flagQuadraticForm` (`FlagAlgebra/QuadraticForm.lean`), `wᵀQv` is `kernelCombo` | the certificate consumes PSD blocks directly (`hQ : (Qs i).PosSemidef`, symmetry included in `PosSemidef`); conclusion (2) is `φ₀ ⟦(wᵀQv)²⟧₀ ≤ ⟨Qw,w⟩·Δ` with `⟨Qw,w⟩ = w ⬝ᵥ Q *ᵥ w`; conclusions (3)–(4) put the moment vector in `ker Q` (`Q *ᵥ χ(v) = 0`), a.s. and on all of `S_{σₜ}(Y)`; the rank/row-space sentence is unformalised linear-algebra prose (Deviation 13e) |
| `prop:unique-slice-stability` (Prop 82) | `unique_slice_stability` ([`RelativeSlackness.lean`](./RelativeSlackness.lean)) | `Z` closed, slice `{φ ∈ Z ∣ ∀ j, φ(h_j) = c_j} = {φ*}` ⟹ every sequence in `Z` with converging densities converges to `φ*`; the index family is arbitrary (Deviation 13c — countability is unnecessary) |

**§11.4–§11.8 audit map** (paper label ↦ Lean statement to read; the paper's
§11.4–§11.8 environments share one counter with §11.2–§11.3, which ended at Prop 82 / Remark 83):

| `paper.tex` (paper #) | Lean statement to read | What to verify |
|---|---|---|
| `def:relative-plantability` (Def 84) | `relQσ` ([`RelativePlanted.lean`](./RelativePlanted.lean)), `RelativelyRootPlantable` | `Q_σ(Y)` = the points of `X_σ` that are density limits of finite σ-flags whose underlying graphs are in the class and whose unlabelled flags converge into `closure Y`; relatively root-plantable ⇔ `relSσ Y σ = relQσ hc Y σ` |
| `prop:relative-plantability` (Prop 85) | `relQσ_isClosed`, `relQσ_subset_Qσ`, `support_subset_relQσ`, `relSσ_subset_relQσ`, `relQσ_Q0_eq`, `relativelyRootPlantable_Q0_iff`, `relQσ_nonneg_implies_relEnsemble`, `relative_planted_criterion` (all [`RelativePlanted.lean`](./RelativePlanted.lean)) | the structure clauses: closedness (diagonal argument), `Q_σ(Y) ⊆ Q_σ`, `supp ℙ[φ₀] ⊆ Q_σ(Y)` hence `S_σ(Y) ⊆ Q_σ(Y)` (finite rooting distributions ⇒ extension measure, weak convergence + portmanteau), `Q_σ(Q₀) = Q_σ` (so `Y = Q₀` recovers absolute root-plantability), and part (ii): non-negativity on `Q_σ(Y)` ⟹ relative ensemble semantics, equivalent for every `f` iff relatively root-plantable |
| `prop:mantel-not-plantable` (Prop 86) | `mantel_not_relatively_plantable` ([`MantelNotPlantable.lean`](./MantelNotPlantable.lean)), witness `exists_mantel_planted_view_edge_zero`, host `knnPlusW`; **`hpin` discharged:** `mantel_not_relatively_plantable_of_uniqueness` ([`TuranSliceIdentities.lean`](./TuranSliceIdentities.lean)) | conclusion `relSσ mantelSlice vtype ⊂ relQσ … mantelSlice vtype` (strict); the witness is the parity-bipartite `K_{n+1,n+1}` + isolated root (Deviation 14g), giving a planted view with `χ(e) = 0`; the pinning input `hpin` (every relative-support point has `ψ(e) = 1/2`) is Thm 92(i) — either the explicit hypothesis of the original form (Deviation 14a), or supplied by `relative_mantel_vtype` in the `_of_uniqueness` form, which needs only the Erdős–Simonovits hypothesis `hES` |
| `thm:relative-certificate-gap` (Thm 88) | `no_relative_closed_certificate_gap` ([`RelativeCertificateGap.lean`](./RelativeCertificateGap.lean)); `YWithin` / `MemYClosure` / `relEnsCone`; crux `relEnsCone_subset_closure_quotCone` | the quotient SOS cone and the relative ensemble cone (non-negative on `S_σ(Y)`) have the same `‖·‖_Y`-seminorm closure, in the same ε-form as §10 (Deviation 12a); mind the `S_σ(Y) = ∅` degenerate branch |
| `thm:relative-positivstellensatz` (Thm 89) | `relative_positivstellensatz` ([`RelativePositivstellensatz.lean`](./RelativePositivstellensatz.lean)), `relative_positivstellensatz_closure` | slice-valid ⇔ for every `ε > 0` some finite penalty `M·∑ g_{j_i}²` makes `f + ε·1₀ + M·∑ g²` class-valid (compactness of `Q₀` + finite-intersection on the sublevel sets); the closure form: `Y`-non-negative = `‖·‖_{Q₀}`-closure of `C_{Q₀} + span{gⱼ²}`; holds for `Y = ∅` too |
| `thm:turan-slice` (Thm 91) | existence: `turanSlice` ([`TuranLimit.lean`](./TuranLimit.lean)), `turanSlice_nonempty`, `exists_turan_limit`; the fixed limit `turanLimit` ([`TuranDirac.lean`](./TuranDirac.lean)) with `turanLimit_mem_slice`; **identity halves**: `turan_slice_identity_vtype` ([`TuranSliceIdentities.lean`](./TuranSliceIdentities.lean)), `_edge`, `_nonEdge`, via the singleton supports `turanLimit_relSσ_vtype` / `_edge` / `_nonEdge` | the existence half is unconditional; the identity halves (i)–(iii) hold under `hES : turanSlice r ⊆ {posHomPoint (turanLimit r hr)}` — check this is **equivalent** to the paper's "exactly one point" (`turanLimit_mem_slice` gives `⊇` unconditionally) and that the pinned values match the paper: `e = (r-1)/r`; `a_τ = b_τ = 1/r`, `g_τ = (r-2)/r`, `z_τ = 0`; `z_η = 1/r`, `g_η = (r-1)/r`, `a_η = b_η = 0` (dictionary: Deviation 15d). The route is transitivity→Dirac (`labelExtensions_turan_{vtype,edge,nonEdge}_subsingleton`, [`TuranAut.lean`](./TuranAut.lean); `extend_eq_dirac_of_labelExtensions_subsingleton`, [`TuranDirac.lean`](./TuranDirac.lean) — Deviation 15a) |
| `thm:relative-mantel` (Thm 92) | `mantelSlice` ([`TuranLimit.lean`](./TuranLimit.lean)), `mantelSlice_nonempty`; clause (i): `relative_mantel_vtype` ([`TuranSliceIdentities.lean`](./TuranSliceIdentities.lean)) | existence = `turanSlice 2`; clause (i) — the relative-support edge pinning at `1/2` — is now a theorem under `hES` (exactly `MantelNotPlantable`'s `hpin`); the `τ`/`η` clauses are the `r = 2` instances of the Thm 91 parametric identities |
| `prop:equality-slice-vanishing` (Prop 94) | `equality_slice_vanishing` ([`CertificateSliceVanishing.lean`](./CertificateSliceVanishing.lean)), `eqSlice` | a certificate `h + ∑ λᵢ ⟦ℓᵢ²⟧₀ ≤ c·1₀` on `Q₀` (`λᵢ > 0`) forces `ψ(ℓᵢ) = 0` for every `ψ ∈ S_{σᵢ}(Y)` over the slice `Y = eqSlice forb0 h c`; this is `relative_slackness_global_sq` with `fᵢ := ℓᵢ²`, `n := 0` |
| `thm:k4free-p4-equality-slice` (Thm 95) | `k4freeP4_eta_equation` ([`ParametricP4Slice.lean`](./ParametricP4Slice.lean)), `k4freeP4_tau_symm`, `k4freeP4_tau_equation`; slice `k4freeP4Slice`, `k4freeP4Slice_eq_parametric` | the `r = 3` slice equations, **unconditional** (the `κ₄` coefficient vanishes at `r = 3`, so no Zykov input); the slice is stated with the `K4freeP4.P4_density` four-atom form as in the paper, shown equal to the parametric slice; **Tier-2 axioms** (certificate consumers) |
| `thm:parametric-p4-equality-slice` (Thm 97) | `parametricP4_eta_equation`, `parametricP4_tau_symm`, `parametricP4_tau_equation`, `parametricP4_K4_density`; slice `parametricP4Slice`; certificate bridge `parametricP4_cert` (all [`ParametricP4Slice.lean`](./ParametricP4Slice.lean)) | the mined equations `(r-1)·z_η = g_η` on `S_η(Y_r)`, `a_τ = b_τ` and `(r-2)(a_τ+b_τ) = 2g_τ` on `S_τ(Y_r)`, and the extremal `K₄` density `(r-1)(r-2)(r-3)/r³` on `Y_r`; the Zykov bound is the explicit hypothesis `hZykov` (Deviation 14a); **Tier-2 axioms** |
| `thm:parametric-moments` (Thm 99) | `Graphon.moments_T` ([`GraphonMoments.lean`](./GraphonMoments.lean)), `moments_D`, `moments_variance`, `moments_interval`, `moments_regular_iff` | kernel level, on `unitInterval` graphons (Deviation 14b): from `R_τ = 0` / `R_η = 0` (the a.e. forms are `Rtau_eq_zero_iff_ae` / `Reta_eq_zero_iff_ae`), the identities (i)–(iv): `(r-1)T = (r-2)D`, `r(2r-3)D = (r-1)²(3p-1)`, `D - p² = (α⁺-p)(p-α⁻)`, `α⁻ ≤ p ≤ α⁺` with degree-regularity exactly at the endpoints |
| `thm:slice-rigidity` (Thm 100) | `Graphon.slice_rigidity` ([`GraphonRigidity.lean`](./GraphonRigidity.lean)) | conclusion in **measurable-partition form** (Deviation 14c): a measurable `P : I → Fin r` with all fibers of volume `1/r` such that a.e. `W = 0` on same-colour and `W = 1` on different-colour pairs — the paper's "up to relabelling, `T_r`" minus the cosmetic relabelling |
| `cor:r3-rigidity` (Cor 101) | `Graphon.r3_rigidity` ([`GraphonRigidity.lean`](./GraphonRigidity.lean)) | at `r = 3` the endpoints coincide, so the edge-density hypothesis disappears: the two local equations alone force the balanced tripartite partition form |
| `thm:k4free-p4-tripartite` (Thm 102) | `k4free_p4_tripartite_of_represents` / `k4free_p4_tripartite_of_rep_exists` ([`GraphonRepresentation.lean`](./GraphonRepresentation.lean)); kernel engine `k4freeP4_graphon_tripartite` ([`GraphonKernelTransport.lean`](./GraphonKernelTransport.lean)) | the rooted transport discharges both `r3_rigidity` hypotheses from the `K₄`-free `P₄`-slice membership `hmem`; `k4free_p4_tripartite_of_represents` composes this with profile agreement to give the **unconditional, paper-verbatim** statement, quantified over *representing* graphons (no representation-existence input — the paper's own quantifier shape); `_of_rep_exists` additionally supplies the existence half, conditional on the one named classical input `hrep` (Lovász–Szegedy existence); its hom avatar still separately enters [`SliceRecovery`](./SliceRecovery.lean) as the `huniq` hypothesis for Cor 104, untouched by this closure |
| `cor:k4free-p4-qualitative-stability` (Cor 104) | `k4free_qualitative_stability` ([`SliceRecovery.lean`](./SliceRecovery.lean)) | every `K₄`-free sequence with `P₄` density `→ 32/9` converges to the balanced tripartite limit, **given** the singleton slice identification `huniq` (= Thm 102's conclusion, hypothesis-ised) |
| `cor:parametric-p4-turan-recovery` (Cor 105) | `parametric_recovery` ([`SliceRecovery.lean`](./SliceRecovery.lean)); the "consequently" clauses `parametric_recovery_identities` ([`TuranSliceIdentities.lean`](./TuranSliceIdentities.lean)) | the first half: under `hZykov` and the Zykov **equality case** `hZykEq`, the parametric slice collapses to `{χ★}`; the "consequently" support identities then follow at all three types (composing with the `turanLimit_relSσ_*` singletons). Mind the benign deviation `3 ≤ r` vs the paper's `r ≥ 4` (Deviation 15c); **Tier-2 axioms** |
| `cor:top-endpoint-recovery` (Cor 106) | `parametricP4_graphon_top_endpoint_rigidity` (kernel level), `parametricP4_top_endpoint_of_represents` / `_of_rep_exists` (paper-verbatim / `hrep`-conditional) ([`GraphonParametricTransport.lean`](./GraphonParametricTransport.lean)) | the same pattern as Thm 102, run at general `r ≥ 3`: `Graphon.slice_rigidity` with the edge-density pin `edgeDensity = α_r⁺` (in place of the Zykov equality case) discharged from slice membership, then composed with profile agreement into the representative-quantified, `hrep`-conditional forms |
| `cor:parametric-qualitative-stability` (Cor 107) | `parametric_qualitative_stability` ([`SliceRecovery.lean`](./SliceRecovery.lean)) | extremal `P₄`-density sequences converge to `χ★`, under `hZykov`/`hZykEq`/`hne` (via `unique_slice_stability`); **Tier-2 axioms** |
| `thm:approximate-moments` (Thm 109) | `Graphon.approximate_moments` ([`GraphonMoments.lean`](./GraphonMoments.lean)), `_interval`, `_variance` | certificate-free, for **every** graphon: the moment-identity deviations are `≤ (r-1)·√R_η + ((r-2)/2)·√R_τ` |
| `prop:k4free-p4-certificate-stability` (Prop 110) | hom level: `parametricP4_sq_bounds` ([`ParametricP4Slice.lean`](./ParametricP4Slice.lean)); kernel level: `Graphon.RtauMinus`, `graphonHom_f₂_eq_RtauMinus`, `parametricP4_graphon_RtauMinus_le`/`_eq_zero` ([`GraphonParametricTransport.lean`](./GraphonParametricTransport.lean)) | the certificate square bounds — the `9/8`, `1/5`, `9/35` pattern after dividing by the coefficients; the kernel functional `R_τ⁻ = ∫∫W(d(x)−d(y))²` **is now defined**, with the hom→kernel bridge `graphonHom_f₂_eq_RtauMinus : φ_W(f₂) = R_τ⁻(W)` (via the extension-measure spec, no new density computations) replacing the former bare `R`-bound hypothesis; **Tier-2 axioms** (both halves) |
| `thm:k4free-p4-quant-stability` (Thm 111) | `Graphon.r3_edge_sq_bound` ([`GraphonQuantStability.lean`](./GraphonQuantStability.lean)), `r3_degree_concentration`, `r3_edge_density_stability`, `r3_certificate_instance`, `stability_via_modulus` | the `r = 3` chain: `(3p-2)² ≤ C`, `9·∫(d-p)²` concentration, `|p - 2/3| ≤ (1/3)√C` with the `(3/√2 + 3/(2√35))√Δ` certificate instance, and the final implication with `ω_Tur` abstracted as a target-predicate modulus `hmod` (`δ□` not formalised — Deviation 14d) |
| `thm:parametric-quant-stability` (Thm 112) | (i) `parametricP4_sq_bounds` ([`ParametricP4Slice.lean`](./ParametricP4Slice.lean)), `parametricP4_graphon_RtauMinus_le` ([`GraphonParametricTransport.lean`](./GraphonParametricTransport.lean)); (ii) `parametricP4_K4_density_approx`; (iii) `Graphon.interval_localisation` ([`GraphonQuantStability.lean`](./GraphonQuantStability.lean)), `interval_localisation_below`, `quadratic_confinement`, `moment_deviation_bound`; (iv) `parametric_stability_via_modulus`, `parametric_graphon_stability_via_modulus` ([`ParametricStabilityModulus.lean`](./ParametricStabilityModulus.lean)) | (i) hom level plus the kernel-level third clause; (ii) hom level, notably **without** Zykov input; (iii) formalised on **both** sides (quadratic confinement + both interval-localisation halves, `r ≥ 4`); (iv) the `ω_Zyk` route is **now formalised** — also **without** needing the Zykov bound hypothesis (only the assumed modulus `hmod` is classical content); the hom halves are **Tier-2** |

**Statements worth the closest reading** (their Lean encoding involves a modelling choice you should
confirm is faithful, rather than a routine transcription): `FinitePlanting` and `SparseRootRepair`
(the quantifier structure and the sum-type host), and the planting `def`s `oneRootPlant`/`twoRootPlant`
(the `Adj` match arms). Everything else is a direct transcription. The documented deviations
(coupling-free counting, sum-type→`Fin N` presentation, `hrs`, the `maxHeartbeats` raises) are listed
in [Notable deviations](#notable-deviations-from-the-paper) Deviation 8.

**Mechanical re-verification** (reproduces the claims above, ~minutes after `lake exe cache get`):

```bash
lake build LeanFlagAlgebras.MetaTheory                                  # 8018 jobs, green
grep -rnwE 'sorry|admit|native_decide' LeanFlagAlgebras/MetaTheory --include='*.lean'   # → no output
printf 'import LeanFlagAlgebras.MetaTheory\nopen FlagAlgebras.MetaTheory\n%s\n' \
  '#print axioms finitePlanting_root_plantable
#print axioms sparseRootRepair_finitePlanting
#print axioms c5free_one_root_plantable
#print axioms c5free_two_root_nonedge_plantable
#print axioms pinning_obstruction
#print axioms degenerate_not_rootPlantable
#print axioms c4free_not_rootPlantable
#print axioms coC4free_not_rootPlantable
#print axioms edgeDegenerate_of_subquadratic
#print axioms complementation_invariance
#print axioms no_interior_pinning
#print axioms c5free_edge_not_rootPlantable
#print axioms relSσ_closure_eq
#print axioms relative_soundness
#print axioms relative_criterion
#print axioms relative_slackness_global
#print axioms downward_cauchy_schwarz
#print axioms certificate_first_moment_sq_bound
#print axioms unique_slice_stability
#print axioms kernel_slackness_global
#print axioms relative_planted_criterion
#print axioms relative_positivstellensatz
#print axioms no_relative_closed_certificate_gap
#print axioms mantel_not_relatively_plantable
#print axioms equality_slice_vanishing
#print axioms exists_turan_limit
#print axioms turan_slice_identity_vtype
#print axioms mantel_not_relatively_plantable_of_uniqueness
#print axioms Graphon.slice_rigidity
#print axioms Graphon.approximate_moments
#print axioms graphonHom
#print axioms graphonProfile_zeroSpaceProp
#print axioms rootedViewMeasure_eq_extend' > /tmp/chk8.lean
lake env lean /tmp/chk8.lean        # each → [propext, Classical.choice, Quot.sound]

# the Tier-2 certificate consumers additionally print the two compiled-evaluation axioms:
printf 'import LeanFlagAlgebras.MetaTheory\nopen FlagAlgebras.MetaTheory\n%s\n' \
  '#print axioms parametricP4_tau_equation
#print axioms parametric_qualitative_stability
#print axioms parametric_recovery_identities
#print axioms k4freeP4_graphon_tripartite
#print axioms parametricP4_top_endpoint_of_represents
#print axioms parametric_stability_via_modulus' > /tmp/chk11.lean
lake env lean /tmp/chk11.lean       # each → [propext, Classical.choice, Quot.sound, Lean.ofReduceBool, Lean.trustCompiler]
```

---

## How the existing flag-algebra formalisation enabled this

This meta-theory is a layer **on top of** the repository's existing formalisation of flag algebras
(`LeanFlagAlgebras/FlagAlgebra/`, `LeanFlagAlgebras/Forbid/`). That base supplied the entire
*semantic foundation* — Razborov's flag algebra, its homomorphism space, the random-extension
measure, the density and rooting machinery — so the §1–11 results could be **stated and proved by
reusing deep existing results rather than re-deriving the framework**. This is what reduced the task
from "formalise flag algebras *and then* the meta-theory" to "formalise the meta-theory, reusing
the flag algebras", and is the single biggest reason a `sorry`-free development was feasible. (§6–§7
add a second layer of reuse on top — they are built by reusing §5, see the §6–§7 row of the results
table and Deviation 5 — §8 a third, reusing the §5/§7 capstone toolkit, see item 9 below; §9 a
fourth, reusing §5's constrained representation, §8's diagonal/finite-planting pattern, the §4
cylinder/Portmanteau tail, and the §9.1 degeneracy template, see item 10; §10 rests on the §4
support machinery, the moment-uniqueness theorem, and Stone–Weierstrass; and §11.2–§11.3 re-runs the
§4 support-closure argument over an arbitrary constraint set and reuses the base library's
Cauchy–Schwarz and quadratic-form lemmas — see Deviations 12–13.) Concretely:

1. **The objects to talk about already existed.** `FlagAlgebra σ` (the algebra `A^σ`, with
   `basisVector`, the product, `flagDensity_self`), `PositiveHom σ`, and — crucially — the **compact
   metric homomorphism space `PositiveHomSpace σ` (`X_σ`)** with its `CompactSpace`/`MetricSpace`/
   closedness instances and coordinate continuity (`FinFlag.continuous`). Because `X_σ` and its
   topology were already in place, §2–§4 (`Q_σ`, `S_σ`, the support-closure criterion) could be
   phrased *directly* as topology/measure statements about `X_σ`, with no need to build the space.

2. **The representation theorem — and its proof *technique* — was reusable.**
   `positiveHom_as_flagSeq_limit` / `flagSeq_limit_mem_positiveHom` (FlagSequence) realise points of
   `X_σ` as graph limits. Its proof goes through a probabilistic construction — `flagSeqMeasure`,
   `randomDensity_expectation`, `flagSeqMeasure_error_prob_zero`. The **single hardest new result**,
   the constrained representation theorem (`ConstrainedRep`), was obtained by *adapting that very
   machinery*: intersecting the existing full-measure convergence event with a new full-measure
   "forbidden-free" event. Without the existing `flagSeqMeasure` development this step would have
   meant redeveloping the whole representation theorem from scratch.

3. **The random-extension measure `ℙ[φ₀]` gave the ensemble semantics for free.**
   `probMeasure_extend_emptyType_positiveHom` together with its **defining integral identity**
   (`…_spec`: `∫ φ f dℙ[φ₀] = φ₀⟦f⟧₀ / φ₀⟨σ⟩₀`, Razborov 3.5) is what "ensemble non-negativity" and
   the §3 *support-passes* lemma are manipulations of. The surrounding tightness/weak-convergence
   results — `flagDensitySpace_probMeasure_isSeqCompact` (Prokhorov),
   `exists_converge_flagSeq_and_probMeasure_tendsto`,
   `tendsto_integral_flagDensitySpace_of_converge_flagSeq`,
   `increasing_flagSeq_contain_convergent_subseq` — reduced `WeakConvergence`'s hard
   "`P_M ⇒ ℙ[φ₀]`" theorem to a subsequence-uniqueness argument over existing lemmas, instead of
   from-scratch measure theory.

4. **The rooting measure and its combinatorics collapsed the capstone's crux.** `FinFlag.toPMF` /
   `FinFlag.toProbMeasure` (the σ-rooting probability measure, weighted by
   `downwardNormalizingFactor`) and the count identities `isomorphismCount`, `labelExtensions`, and
   `isoInjectiveMapSet_card_eq_sum_labelExtensions_isomorphismCount_mul_labeledGraphCount` (all in
   FlagOperators) were exactly what `RootingUniform` and the crux `planted_cylinder_mass` needed:
   because `isomorphismCount` *already* counts σ-rootings per isomorphism class, the feared
   measure-↔-embedding bridge became a short regrouping rather than a several-hundred-line
   development.

5. **Flag density as a count, and the labelled-graph machinery, underpin the whole planted
   estimate.** `flagDensity₁`, `flagDensity_self` (a flag has density `1` in itself — the
   *self-forbidding* trick), `labeledGraphCount`, `subflagDensity`, and
   `LabeledGraph` / `LabeledSubgraph` / `inducedLabeledSubgraph` / `≃f` (`LabeledGraphIso`) from
   `FlagDef` drive `DensityBridge`, `LabeledCount`, `CloneCount`/`CloneTotal`/`PlantedCount`,
   `PlantedEstimate`, and the heredity lemmas in `GraphClassConstraint`.

6. **The labelled/unlabelled bridge was already built.** The `downward` operators (`⟦·⟧₀`),
   `⟨σ⟩₀` (`flagType_asEmptyTypeAlgebra`), and `downwardNormalizingFactor` are the translation
   between the σ-labelled and `∅ₜ`-unlabelled (graph) worlds that §3 and §5 cross constantly.

7. **The single-forbidden-flag pattern was the template to generalise.** `Forbid/Basic`'s
   `forbidEq` / `forbidLE` (reasoning conditioned a.s. on one forbidden flag) is conceptually what
   the `Constraint` / `GraphClass` framework here generalises to an entire forbidden family.

8. **Mathlib provided the analytic finale on top of the repo base:** Stone–Weierstrass and Urysohn
   (the support-closure criterion), closed-set Portmanteau and `Measure.support` (the capstone's
   limit step), `Ideal.Quotient` (the §3 quotient algebra), and `SimpleGraph.CliqueFree.comap`
   (`K_r`-free heredity).

9. **§8 reused the §5/§7 *meta-theory* layer, almost verbatim.** `thm:finite-local-planting` is
   structurally the §5 capstone `clone_root_plantable` with the blow-up sequence replaced by the
   abstract planting family `Hₜ`. It reuses **the construction-agnostic capstone toolkit
   [`CapstoneShared`](./CapstoneShared.lean)** exactly as that module's header anticipated ("reusable
   for §8+"): `mem_closure_of_forall_finset_cylinder` (reduce `ψ ∈ S_σ` to finite cylinders),
   `cyl`/`isClosed_cyl` (the closed set for Portmanteau), `flagDensity₁_respect_eqv`, and crucially
   `toProbMeasure_apply_eq_labeling_ratio` + `card_labelings_eq_card_embeddings` (which turn the
   planting's `|Θ| ≥ δ|V|^k` directly into `P_t(C̃) ≥ δ`). It reuses **`tendsto_rootingMeasure_extend`**
   ([`WeakConvergence`](./WeakConvergence.lean)) unchanged — that lemma was already proved for *any*
   convergent flag sequence, so the §8 family `Hₜ` (not a blow-up) feeds it directly — and the §4
   support/Portmanteau tail (`Sσ_subset_Qσ`, `mem_Qσ_iff`, `Measure.support`,
   `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), the constrained representation
   `exists_constrained_flagSeq_limit`, the subsequence-limit lemmas
   (`increasing_flagSeq_contain_convergent_subseq`, `flagSeq_limit_mem_positiveHom`), and
   `subgraphDensity`/`subgraphCount` (for the uniform `σ`-type-density lower bound). The `C₅`-free
   class is a one-line [`HeredClass`](./HeredClass.lean) instance over Mathlib's
   `SimpleGraph.IsContained`/`Free`/`Copy` and `cycleGraph`, and `lem:c5-nbhd` is pure Mathlib graph
   theory (`induce`, `edgeFinset`, walks/paths, `IsTree.card_edgeFinset`, `girth`). `lem:c5-blowup`
   reuses §5's `independentBlowup`.

10. **§9 (obstructions) reused the §5/§8 *meta-theory* layer and Mathlib's probability.** The
    degeneracy obstructions (§9–§9.2) and the §9.5 `C₅`-edge obstruction route through the abstract
    `pinning_obstruction` (`Pinning`) and reuse the §9.1 `C4Free` degeneracy template wholesale (the
    density-→0 squeeze, `flagDensity₁_eq_subset_count_div` subset-counting, the `StarWitness`
    quotient-point assembly — `exists_Qσ_point_flag_eq` is its any-`σ`/any-flag generalisation), with
    `lem:c5-few-triangles` resting on §8's `lem:c5-nbhd`. §9.4's edge-thinning stack reuses
    `exists_constrained_flagSeq_limit` (§5), the §8 `FinitePlanting` diagonal-extraction pattern, the
    §4 cylinder/Portmanteau tail (`CapstoneShared.mem_closure_of_forall_finset_cylinder`), and the
    `RandomHom` extension spec — adding only the genuinely new probabilistic core (random
    edge-thinning over `Measure.pi`, the second-moment/Chebyshev realization, and the `λ→0`
    edgeless-cloud boolean point), a McDiarmid-free route (Deviation 10).

What is genuinely **new** here — not present in the existing formalisation — is the meta-theory
layer itself: the constrained class and quotient (§3), the support-closure criterion (§4), the
independent blow-up with its planted estimate and the reusable `GraphClass` packaging, the capstone
(§5), the constrained representation theorem, for §8 the finite-planting criterion, the
coupling-free sparse-repair counting bound, and the `C₅`-free planting constructions, and for §9 the
pinning obstruction, the degeneracy/complementation machinery, the random edge-thinning concentration
(§9.4), and the `C₅`-free book-edge obstruction (§9.5). These are built *with*, but go beyond, the
flag-algebra base.

---

## Repository layout (this directory)

* **`paper.tex`** — the source article; §1–10 (all subsections) and the §11.2–§11.8 relative
  (slice) theory are formalised here (§11.4–§11.8 with the partial-coverage caveats listed in
  [Scope & limitations](#scope--limitations)).
* **`*.lean`** — 95 modules (see [`ARCHITECTURE.md`](./ARCHITECTURE.md) for the full map). Notable
  groups: the Cor 106 / Thm 112(iv) closures —
  [`GraphonParametricTransport.lean`](./GraphonParametricTransport.lean) (the general-`r` rooted
  transport, the `R_τ⁻` kernel functional, and Cor 106) and
  [`ParametricStabilityModulus.lean`](./ParametricStabilityModulus.lean) (Thm 112(iv)); the Thm 102
  closure — [`GraphonRepresentation.lean`](./GraphonRepresentation.lean) and the step-graphon
  density modules [`GraphonStep.lean`](./GraphonStep.lean)/[`GraphonCounting.lean`](./GraphonCounting.lean);
  the five-module **rooted transport** ([`HOM_TO_GRAPHON_DESIGN.md`](./HOM_TO_GRAPHON_DESIGN.md)) —
  [`StdRootedBridge`](./StdRootedBridge.lean), [`GraphonRootedDensity`](./GraphonRootedDensity.lean),
  [`GraphonRootedHom`](./GraphonRootedHom.lean), [`GraphonRootedMeasure`](./GraphonRootedMeasure.lean)
  and the capstone [`GraphonKernelTransport`](./GraphonKernelTransport.lean) — carrying the `K₄`-free
  `P₄`-slice equations into `r3_rigidity`'s a.e. kernel hypotheses
  (`k4freeP4_graphon_tripartite`); and the `φ_W` infrastructure (every graphon is a positive
  homomorphism) — [`GraphonInducedDensity`](./GraphonInducedDensity.lean),
  [`PairSubsetCount`](./PairSubsetCount.lean), [`EmptyTypeGraphBridge`](./EmptyTypeGraphBridge.lean)
  and [`GraphonHom`](./GraphonHom.lean). They are
  imported and re-exported by [`../MetaTheory.lean`](../MetaTheory.lean), the aggregator, which in
  turn is in the top-level build manifest `../../LeanFlagAlgebras.lean`.
* **`README.md`** (this file), **`ARCHITECTURE.md`**, **`READING_GUIDE.md`** — documentation.

This `MetaTheory` development is built *on top of* the main `LeanFlagAlgebras/` formalisation of
flag algebras and adds new theory rather than re-deriving that machinery — see
[How the existing flag-algebra formalisation enabled this](#how-the-existing-flag-algebra-formalisation-enabled-this)
above, and the repository's top-level `CLAUDE.md` for the overall flag-algebra codebase.

---

## Scope & limitations

* **Formalised:** the proved results of §1–10, plus the §11.2–§11.8 relative (slice) theory (above) —
  including §6 (complete blow-ups / true twins,
  `thm:true-clone-root-plantable`, `cor:cluster-graphs`), §7 (substitution-closed classes,
  `thm:substitution-root-plantable`), obtained by generalising the §5 planted estimate to the
  generalised blow-up `subBlowup` (`SubstitutionBlowup`/`SubstitutionEstimate`/`SubstitutionClosed`),
  and §8 (the finite-local-planting criterion `thm:finite-local-planting`, `thm:sparse-repair-planting`,
  and the `C₅`-free root-plantability results `thm:c5-one-root`/`thm:c5-nonedge-root` with `lem:c5-nbhd`
  and `lem:c5-blowup`) in the `FinitePlanting`/`SparseRootRepair`/`C5Free`/`C5OneRoot`/
  `C5TwoRootNonEdge`/`C5Blowup` modules, plus **all of §9** — the abstract pinning obstruction
  (`thm:pinning`) in `Pinning`; **§9.1 / §9.2** — the degeneracy obstruction
  (`thm:degenerate-obstruction`), the `C₄`-free counterexample (`lem:c4-edge-zero`,
  `cor:c4-counterexample`), the general family criterion (`cor:degenerate-family`), and the dense
  complement obstruction (`cor:codegenerate`) — in `EdgeObstruction`/`StarWitness`/`C4Free`/
  `DegenerateFamily`/`DenseObstruction`; **§9.4** — the boundary / no-interior theorem
  (`thm:no-interior`, `subsec:boundary`) in the edge-thinning stack `NoInterior`/`EdgeThinning`/
  `EdgeThinningLimit`/`NoInteriorThinning` (McDiarmid-free, Deviation 10); and **§9.5** — the
  `C₅`-edge obstruction (`thm:c5-edge-not-root-plantable`, `sec:c5-edge`) with `lem:c5-few-triangles`,
  the book-graph quotient point, and the no-vtype-obstruction corollary (`cor:c5-no-pin`) in
  `C5FewTriangles`/`C5EdgeObstruction`. `lem:complementation` (Lemma 50) is also formalised, via the
  complement homeomorphism (Deviation 9b). **§10** (`sec:empty-type`, "the gap is invisible to
  density bounds": `prop:empty-type`, `cor:confined`, `thm:no-closed-certificate-gap`,
  `prop:ideal-zero`, `prop:single-point`, `cor:c5-edge-closed-inert`) is formalised in the
  `DownwardAverage`/`EmptyTypeCollapse`/`CertificateCones`/`VanishingIdeal`/`BooleanPoint`/
  `SinglePoint`/`C5EdgeInert` modules (Deviation 12). **§11.2–§11.3** (the relative-ensemble
  foundation of the slice method: the relative support `S_σ(Y)` with `lem:relative-closure` /
  `prop:relative-soundness` / `prop:relative-criterion`, and complementary slackness
  `thm:relative-slackness` / `lem:relative-cauchy-schwarz` / `cor:sos-first-moments` /
  `thm:kernel-slackness` / `prop:unique-slice-stability`) is formalised in the
  `RelativeSupport`/`RelativeClosure`/`RelativeSlackness`/`KernelSlackness` modules (Deviation 13).
  **§11.4–§11.8** (the slice method and the graphon layer: `def:relative-plantability` /
  `prop:relative-plantability` / `prop:mantel-not-plantable` / `thm:relative-certificate-gap` /
  `thm:relative-positivstellensatz`; `thm:turan-slice` / `thm:relative-mantel` — existence
  unconditional, the identity halves under the named Erdős–Simonovits hypothesis `hES`
  (Deviation 15); `prop:equality-slice-vanishing` and the `K₄`-free-`P₄` slice theorems
  `thm:k4free-p4-equality-slice` / `thm:parametric-p4-equality-slice`, fed by the verified
  `CompleteGraphFreeP4.gap_identity` certificate; the kernel-level `thm:parametric-moments` /
  `thm:slice-rigidity` / `cor:r3-rigidity` / `thm:approximate-moments` /
  `thm:k4free-p4-quant-stability` / `thm:parametric-quant-stability`(i)–(iii); and the recovery /
  qualitative-stability corollaries Cor 104/105/107, Cor 105 complete including its
  "consequently" identities) is formalised in the
  `RelativePlanted`/`RelativeCertificateGap`/`RelativePositivstellensatz`/
  `CertificateSliceVanishing`/`ParametricP4Slice`/`TuranLimit`/`MantelNotPlantable`/`SliceRecovery`/
  `TuranAut`/`TuranDirac`/`TuranSliceIdentities`
  and `GraphonBasic`/`GraphonMoments`/`GraphonRigidity`/`GraphonQuantStability` modules
  (Deviations 14–15, 18) — **every numbered result of §11 is now formalised**, modulo exactly the
  four permanent classical inputs in the next bullet: Erdős–Simonovits stability, Zykov's
  `K₄`-density bound and its equality case, and Lovász–Szegedy existence enter as named hypotheses
  throughout, in the same shape the paper's (now-revised, Deviation 18) statements name them.
  Building on the graphon layer, the **graphon→hom half of the Lovász–Szegedy representation
  bridge is formalised as infrastructure**: every graphon `W` is a positive homomorphism
  `φ_W ∈ PositiveHom ∅ₜ` (`graphonHom`, [`GraphonHom.lean`](./GraphonHom.lean)), built from the
  induced flag density (`graphonFlagDensity`,
  [`GraphonInducedDensity.lean`](./GraphonInducedDensity.lean)) via the subset-count bridges
  `flagDensity₁_graphFlag`/`flagDensity₂_graphFlag`
  ([`EmptyTypeGraphBridge.lean`](./EmptyTypeGraphBridge.lean),
  [`PairSubsetCount.lean`](./PairSubsetCount.lean)), with the sanity link
  `graphonHom_edge : φ_W(unlabelledEdgeFlag) = W.edgeDensity` (Deviation 16). There is no
  `paper.tex` display for this construction — it is folklore input the §11.7 representation
  results assume. Building further on `graphonHom`, **the full rooted transport
  (`HOM_TO_GRAPHON_DESIGN.md`) is formalised**: the five-module stack
  `StdRootedBridge`/`GraphonRootedDensity`/`GraphonRootedHom`/`GraphonRootedMeasure`/
  `GraphonKernelTransport` carries the `K₄`-free `P₄`-slice equations (mined by
  `ParametricP4Slice`) through the rooted conditional homomorphism and the rooted-view-measure
  identification `rootedViewMeasure_eq_extend` (= `ℙ[φ_W]`) into the a.e. kernel hypotheses of
  `Graphon.r3_rigidity`, discharging both of them unconditionally for any graphon in the slice
  (`k4freeP4_graphon_tripartite`) — the graphon-side content of `thm:k4free-p4-tripartite`
  (Thm 102) (Deviation 17). **The same route then closes the paper-verbatim statements themselves**: Thm
  102 ([`GraphonRepresentation.lean`](./GraphonRepresentation.lean),
  `k4free_p4_tripartite_of_represents` unconditional over representing graphons, plus
  `_of_rep_exists` conditional on `hrep`), **Cor 106** in the identical representative-quantified
  shape ([`GraphonParametricTransport.lean`](./GraphonParametricTransport.lean),
  `parametricP4_top_endpoint_of_represents`/`_of_rep_exists`), and **Thm 112(iv)**
  ([`ParametricStabilityModulus.lean`](./ParametricStabilityModulus.lean),
  `parametric_stability_via_modulus`, which turns out not to need the Zykov bound hypothesis at
  all).
* **Not formalised — by permanent design decision, not a gap:** four classical results are cited
  by the paper itself as unproved external inputs and are never intended to be proved inside this
  development — **Erdős–Simonovits stability** (the singleton claim of Thm 91/92, entering the
  formalised identity halves only as the named hypothesis `hES`), **Zykov's `K₄`-density bound**
  for `r ≥ 4` (`hZykov`) and its **equality case** (`hZykEq`), and **Lovász–Szegedy existence**
  (`hrep`, the one hypothesis behind every `_of_rep_exists`-style corollary above).
  The `hrep` hypothesis alone has a costed retirement path — the weak-regularity campaign of
  [`HOM_TO_GRAPHON_DESIGN.md`](./HOM_TO_GRAPHON_DESIGN.md) — should it ever be undertaken; the
  other three are genuinely permanent (proving them is a different, much larger project — classical
  extremal graph theory, not this meta-theory).
* **Not formalised (future work, all optional):** the general pinning *conjecture*
  (`conj:characterisation`, the tentative general characterisation, not itself a numbered theorem)
  — the one §9 result still open; the **§12 open problems** (prose — nothing to formalise); within
  `cor:degenerate-family`, the non-`C₄` families (general `K_{s,t}` with `s ≥ 3`, even cycles,
  planar), which instantiate `edgeDegenerate_of_subquadratic` via classical extremal bounds
  (Kővári–Sós–Turán, Bondy–Simonovits, the planar edge bound) that are outside the current
  Mathlib, so only the abstract criterion (not those specific instances) is formalised; and two
  further optional campaigns, neither behind an open correctness gap: a **kernel-level
  Mantel/Turán-uniqueness theorem** that would let `hES` be discharged through the graphon⟷hom
  bridge once both its directions exist, and the same **Kővári–Sós–Turán
  (KST)**-type extremal bounds just mentioned for `cor:degenerate-family`. The criterion and
  machinery here are intended to be reusable for any of this remaining, entirely optional work.
* The development reuses results from the surrounding `LeanFlagAlgebras/FlagAlgebra/` directory
  (representation theorem, random-extension measure, Prokhorov compactness, …) as already-proved
  lemmas — these are part of the trusted base, not re-verified here, but they are themselves
  `sorry`-free Lean proofs, not axioms.
