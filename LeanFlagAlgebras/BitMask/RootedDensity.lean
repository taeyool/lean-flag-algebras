import LeanFlagAlgebras.BitMask.RootedMask

/-! # Rooted extraction realizes the labeled induced subflag

The σ-typed analogue of `Density.lean`'s extraction semantics: for a
placement `V ⊇ type_verts` of the right size, the decoding of the
rooted extraction is **flag-isomorphic (label-preservingly)** to the
induced labeled subflag on `V`. The vertex matching sends root position
`i < k` to the host's `i`-th type vertex and position `k + j` to the
`j`-th smallest non-root vertex of `V` — the labeling `rootedVtxList`
reads off. -/

namespace FlagAlgebras.Compute.BitMask

variable {k N m : ℕ} {σ : Sym2FlagType k} {G : Sym2LabeledGraph σ N}

/-! ## Cardinalities -/

/-- A σ-typed graph has exactly `k` type vertices. -/
lemma type_verts_card (G : Sym2LabeledGraph σ N) : G.type_verts.card = k := by
  rw [Sym2LabeledGraph.type_verts_eq_image,
    Finset.card_image_of_injective _ G.type_embed.injective,
    Finset.card_univ, Fintype.card_fin]

/-- A placement of size `m` forces `k ≤ m`. -/
lemma k_le_of_placement {V : Finset (Fin N)} (hTV : G.type_verts ⊆ V)
    (hV : V.card = m) : k ≤ m := by
  have := Finset.card_le_card hTV
  rwa [type_verts_card, hV] at this

/-- The non-root part of a placement has `m − k` vertices. -/
lemma sdiff_card {V : Finset (Fin N)} (hTV : G.type_verts ⊆ V)
    (hV : V.card = m) : (V \ G.type_verts).card = m - k := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTV, type_verts_card, hV]

/-! ## The rooted vertex map -/

/-- The vertex matching of a placement: root positions to the type
vertices (in order), the rest to the ascending non-root vertices. -/
def rootedVmap (G : Sym2LabeledGraph σ N) (V : Finset (Fin N))
    (hTV : G.type_verts ⊆ V) (hV : V.card = m) : Fin m → {x // x ∈ V} :=
  fun i =>
    if h : i.val < k then
      ⟨G.type_embed ⟨i.val, h⟩, hTV (G.mem_type_verts ⟨i.val, h⟩)⟩
    else
      ⟨(V \ G.type_verts).orderEmbOfFin (sdiff_card hTV hV)
          ⟨i.val - k, by have := i.isLt; omega⟩,
        (Finset.mem_sdiff.mp (Finset.orderEmbOfFin_mem _ _ _)).1⟩

/-- The vertex matching reads the rooted vertex list. -/
lemma rootedVmap_val {V : Finset (Fin N)} (hTV : G.type_verts ⊆ V)
    (hV : V.card = m) (i : Fin m) :
    ((rootedVmap G V hTV hV i : {x // x ∈ V}) : Fin N).val
      = (rootedVtxList G V).getD i.val 0 := by
  unfold rootedVmap
  split_ifs with h
  · exact (rootedVtxList_getD_root G V ⟨i.val, h⟩).symm
  · exact (rootedVtxList_getD_nonroot G V (sdiff_card hTV hV)
      (not_lt.mp h)).symm

/-- Roots land in the type vertices, non-roots outside. -/
lemma rootedVmap_mem_type_verts {V : Finset (Fin N)}
    (hTV : G.type_verts ⊆ V) (hV : V.card = m) (i : Fin m) :
    ((rootedVmap G V hTV hV i : {x // x ∈ V}) : Fin N) ∈ G.type_verts
      ↔ i.val < k := by
  unfold rootedVmap
  split_ifs with h
  · exact iff_of_true (G.mem_type_verts ⟨i.val, h⟩) h
  · exact iff_of_false
      (Finset.mem_sdiff.mp (Finset.orderEmbOfFin_mem _ _ _)).2 h

/-- The vertex matching is injective. -/
lemma rootedVmap_injective {V : Finset (Fin N)} (hTV : G.type_verts ⊆ V)
    (hV : V.card = m) : Function.Injective (rootedVmap G V hTV hV) := by
  intro a b hab
  have hval : ((rootedVmap G V hTV hV a : {x // x ∈ V}) : Fin N)
      = ((rootedVmap G V hTV hV b : {x // x ∈ V}) : Fin N) :=
    congrArg Subtype.val hab
  by_cases ha : a.val < k <;> by_cases hb : b.val < k
  · have h1 : G.type_embed ⟨a.val, ha⟩ = G.type_embed ⟨b.val, hb⟩ := by
      have := hval
      unfold rootedVmap at this
      rw [dif_pos ha, dif_pos hb] at this
      exact this
    have h2 := G.type_embed.injective h1
    have h3 : (⟨a.val, ha⟩ : Fin k).val = (⟨b.val, hb⟩ : Fin k).val :=
      congrArg Fin.val h2
    exact Fin.ext h3
  · exfalso
    have hmema := (rootedVmap_mem_type_verts hTV hV a).mpr ha
    rw [hval] at hmema
    exact hb ((rootedVmap_mem_type_verts hTV hV b).mp hmema)
  · exfalso
    have hmemb := (rootedVmap_mem_type_verts hTV hV b).mpr hb
    rw [← hval] at hmemb
    exact ha ((rootedVmap_mem_type_verts hTV hV a).mp hmemb)
  · have h1 : (V \ G.type_verts).orderEmbOfFin (sdiff_card hTV hV)
        ⟨a.val - k, by have := a.isLt; omega⟩
          = (V \ G.type_verts).orderEmbOfFin (sdiff_card hTV hV)
              ⟨b.val - k, by have := b.isLt; omega⟩ := by
      have := hval
      unfold rootedVmap at this
      rw [dif_neg ha, dif_neg hb] at this
      exact this
    have h2 := ((V \ G.type_verts).orderEmbOfFin
      (sdiff_card hTV hV)).injective h1
    have h3 : a.val - k = b.val - k := congrArg Fin.val h2
    refine Fin.ext ?_
    omega

/-- The vertex matching is surjective onto the placement. -/
lemma rootedVmap_surjective {V : Finset (Fin N)} (hTV : G.type_verts ⊆ V)
    (hV : V.card = m) : Function.Surjective (rootedVmap G V hTV hV) := by
  rintro ⟨v, hv⟩
  by_cases hvT : v ∈ G.type_verts
  · rw [Sym2LabeledGraph.type_verts_eq_image] at hvT
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hvT
    refine ⟨⟨t.val, lt_of_lt_of_le t.isLt (k_le_of_placement hTV hV)⟩, ?_⟩
    unfold rootedVmap
    rw [dif_pos t.isLt]
    exact Subtype.ext (by simpa using ht)
  · have hvs : v ∈ V \ G.type_verts := Finset.mem_sdiff.mpr ⟨hv, hvT⟩
    have : ∃ j, (V \ G.type_verts).orderEmbOfFin (sdiff_card hTV hV) j
        = v := by
      have hrange := Finset.range_orderEmbOfFin (V \ G.type_verts)
        (sdiff_card hTV hV)
      have : v ∈ Set.range ((V \ G.type_verts).orderEmbOfFin
          (sdiff_card hTV hV)) := by
        rw [hrange]
        exact hvs
      exact this
    obtain ⟨j, hj⟩ := this
    refine ⟨⟨k + j.val, by have := j.isLt; omega⟩, ?_⟩
    unfold rootedVmap
    rw [dif_neg (show ¬ (k + j.val < k) by omega)]
    refine Subtype.ext ?_
    show ((V \ G.type_verts).orderEmbOfFin (sdiff_card hTV hV)
      ⟨k + j.val - k, _⟩ : Fin N) = v
    rw [show (⟨k + j.val - k, by have := j.isLt; omega⟩ : Fin (m - k)) = j
      from Fin.ext (show k + j.val - k = j.val by omega)]
    exact hj

/-! ## The labeled extraction isomorphism -/

/-- Adjacency in the coerced labeled induced subflag is ambient edge
membership (labeled analogue of `Sym2InducedSubgraph.coe_adj_iff_mem`). -/
lemma labeledCoe_adj_iff_mem (H : Sym2InducedLabeledSubgraph G)
    (u v : ↥(H.toLabeledSubgraph.subgraph.verts)) :
    H.toLabeledSubgraph.coe.graph.Adj u v ↔ s(u.val, v.val) ∈ G.edges := by
  rw [LabeledSubgraph.coe_adj_iff]
  show s(u.val, v.val) ∈ H.edges ↔ _
  simp only [Sym2InducedLabeledSubgraph.edges, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun w hw => ?_⟩
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    exacts [u.2, v.2]

/-- Host bit at the sorted value pair, as edge membership. -/
private lemma host_bit_iff {N : ℕ}
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hostG : Sym2Graph N) {u v : Fin N} (huv : u ≠ v) :
    (maskOfGraph₂ hostG).testBit
        (pairIdx N (min u.val v.val) (max u.val v.val)) = true
      ↔ s(u, v) ∈ hostG.edges := by
  rcases lt_or_gt_of_ne huv with h | h
  · rw [min_eq_left (le_of_lt (show u.val < v.val from h)),
      max_eq_right (le_of_lt (show u.val < v.val from h)),
      testBit_iff_mem_edges₂ h, graphOfMask₂_maskOfGraph₂ hinjN hostG]
  · rw [min_eq_right (le_of_lt (show v.val < u.val from h)),
      max_eq_left (le_of_lt (show v.val < u.val from h)),
      testBit_iff_mem_edges₂ h, graphOfMask₂_maskOfGraph₂ hinjN hostG,
      show (s(v, u) : Sym2 (Fin N)) = s(u, v) from Sym2.eq_swap]

/-- **The rooted extraction decodes to the labeled induced subflag.**
The vertex matching is `rootedVmap`; roots go to roots in order, so the
type embeddings are preserved on the nose. -/
theorem nonempty_rootedExtractIso
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (V : Finset (Fin N)) (hTV : G.type_verts ⊆ V) (hV : V.card = m) :
    Nonempty
      ((labeledGraphOfMask σ m (k_le_of_placement hTV hV)
          (rootedExtractMask m G V (maskOfGraph₂ (underlyingGraph G)))
          (rootedExtractMask_rootsMatch (k_le_of_placement hTV hV)
            hinjN hinjm G V)).toLabeledGraph
        ≃f (⟨V, hTV⟩ : Sym2InducedLabeledSubgraph G).toLabeledSubgraph.coe) := by
  have hbij : Function.Bijective (rootedVmap G V hTV hV) :=
    ⟨rootedVmap_injective hTV hV, rootedVmap_surjective hTV hV⟩
  refine ⟨{ graph_iso := ⟨Equiv.ofBijective _ hbij, ?_⟩,
            type_preserve := ?_ }⟩
  · intro a b
    show (⟨V, hTV⟩ : Sym2InducedLabeledSubgraph
        G).toLabeledSubgraph.coe.graph.Adj
        (rootedVmap G V hTV hV a) (rootedVmap G V hTV hV b) ↔ _
    rw [labeledCoe_adj_iff_mem, labeledGraphOfMask_adj_iff]
    rcases lt_trichotomy a b with hab | rfl | hba
    · have hne : ((rootedVmap G V hTV hV a : {x // x ∈ V}) : Fin N)
          ≠ ((rootedVmap G V hTV hV b : {x // x ∈ V}) : Fin N) := by
        intro h
        exact hab.ne (rootedVmap_injective hTV hV (Subtype.ext h))
      have hb := host_bit_iff hinjN (underlyingGraph G) hne
      rw [show (underlyingGraph G).edges = G.edges from rfl] at hb
      rw [← hb, rootedVmap_val hTV hV a, rootedVmap_val hTV hV b,
        ← rootedExtractMask_testBit hinjm G V _ hab,
        testBit_iff_mem_edges₂ hab]
    · constructor
      · intro hmem
        exact absurd (Sym2.mk_isDiag_iff.mpr rfl)
          (G.edges_valid _ hmem)
      · intro hmem
        exact absurd (Sym2.mk_isDiag_iff.mpr rfl)
          ((graphOfMask₂ m _).edges_valid _ hmem)
    · have hne : ((rootedVmap G V hTV hV b : {x // x ∈ V}) : Fin N)
          ≠ ((rootedVmap G V hTV hV a : {x // x ∈ V}) : Fin N) := by
        intro h
        exact hba.ne (rootedVmap_injective hTV hV (Subtype.ext h))
      have hb := host_bit_iff hinjN (underlyingGraph G) hne
      rw [show (underlyingGraph G).edges = G.edges from rfl] at hb
      rw [show (s(((rootedVmap G V hTV hV a : {x // x ∈ V}) : Fin N),
            ((rootedVmap G V hTV hV b : {x // x ∈ V}) : Fin N))
              : Sym2 (Fin N))
          = s(((rootedVmap G V hTV hV b : {x // x ∈ V}) : Fin N),
              ((rootedVmap G V hTV hV a : {x // x ∈ V}) : Fin N))
          from Sym2.eq_swap,
        show (s(a, b) : Sym2 (Fin m)) = s(b, a) from Sym2.eq_swap,
        ← hb, rootedVmap_val hTV hV a, rootedVmap_val hTV hV b,
        ← rootedExtractMask_testBit hinjm G V _ hba,
        testBit_iff_mem_edges₂ hba]
  · funext t
    refine Subtype.ext ?_
    show ((rootedVmap G V hTV hV
        (Fin.castLE (k_le_of_placement hTV hV) t) : {x // x ∈ V}) : Fin N)
      = _
    unfold rootedVmap
    rw [dif_pos (show (Fin.castLE (k_le_of_placement hTV hV) t).val < k
      from t.isLt)]
    have hre := (⟨V, hTV⟩ : Sym2InducedLabeledSubgraph
      G).toLabeledSubgraph.embed_eq t
    rw [Sym2LabeledGraph.toLabeledGraph_type_embed_eq] at hre
    have hre2 : (((⟨V, hTV⟩ : Sym2InducedLabeledSubgraph
        G).toLabeledSubgraph.coe.type_embed t : _) : Fin N)
          = G.type_embed t := hre
    rw [hre2]
    show G.type_embed ⟨t.val, t.isLt⟩ = G.type_embed t
    exact congrArg G.type_embed (Fin.eta t t.isLt)

/-- Composition of labeled flag isomorphisms (not in the base library). -/
def labeledIso_trans {T : Type} {τ : FlagType T} {V₁ V₂ V₃ : Type}
    {A : LabeledGraph τ V₁} {B : LabeledGraph τ V₂} {C : LabeledGraph τ V₃}
    (e₁ : A ≃f B) (e₂ : B ≃f C) : A ≃f C where
  graph_iso := e₁.graph_iso.trans e₂.graph_iso
  type_preserve := by
    funext t
    show e₂.graph_iso (e₁.graph_iso (A.type_embed t)) = C.type_embed t
    rw [show e₁.graph_iso (A.type_embed t) = B.type_embed t from
      congrFun e₁.type_preserve t]
    exact congrFun e₂.type_preserve t

/-- **Rooted placement criterion, mask form.** A placement carries a
labeled induced copy of the σ-typed pattern `F` iff its rooted
extraction decodes into the labeled class of `F`. -/
theorem labeledCoe_iso_iff_rootedExtract_eqv
    (hinjN : ∀ p₁ ∈ finPairs N, ∀ p₂ ∈ finPairs N,
      pairIdx N p₁.1.val p₁.2.val = pairIdx N p₂.1.val p₂.2.val → p₁ = p₂)
    (hinjm : ∀ p₁ ∈ finPairs m, ∀ p₂ ∈ finPairs m,
      pairIdx m p₁.1.val p₁.2.val = pairIdx m p₂.1.val p₂.2.val → p₁ = p₂)
    (F : Sym2LabeledGraph σ m) (V : Finset (Fin N))
    (hTV : G.type_verts ⊆ V) (hV : V.card = m) :
    Nonempty ((⟨V, hTV⟩ : Sym2InducedLabeledSubgraph G).toLabeledSubgraph.coe
        ≃f F.toLabeledGraph)
      ↔ labeledGraphOfMask σ m (k_le_of_placement hTV hV)
          (rootedExtractMask m G V (maskOfGraph₂ (underlyingGraph G)))
          (rootedExtractMask_rootsMatch (k_le_of_placement hTV hV)
            hinjN hinjm G V) ∼sf F := by
  obtain ⟨e₀⟩ := nonempty_rootedExtractIso hinjN hinjm V hTV hV
  constructor
  · rintro ⟨e⟩
    exact ⟨labeledIso_trans e₀ e⟩
  · rintro ⟨d⟩
    exact ⟨labeledIso_trans e₀.symm d⟩

end FlagAlgebras.Compute.BitMask
