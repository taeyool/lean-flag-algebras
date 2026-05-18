import LeanFlagAlgebras.FlagAlgebra.PositiveHom

/-! # An embedded assertion DSL for flag algebras

An experimental embedded logic over flag-algebra elements. `Assert σ` is an inductive of
atomic equalities (`=ₐ`), inequalities (`≤ₐ`) and implications (`→ₐ`); `eval` interprets
an assertion at a positive homomorphism, `isValid` means it holds for all homomorphisms,
and `Entails` (`⊢ₐ`) is validity of an implication. The file also develops the
equivalence relation `≡ₐ` and the structural/algebraic inference rules of the DSL.
-/

open FlagAlgebras

namespace FlagLogic

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

/-- An assertion of the embedded flag-algebra DSL: an atomic equality `eq` (`=ₐ`) or
inequality `le` (`≤ₐ`) between flag-algebra elements, or an implication `implies`
(`→ₐ`) between assertions. -/
inductive Assert (σ : FlagType (Fin n₀)) where
  -- | false_  : Assert σ
  -- | true_   : Assert σ
  | eq      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  -- | ge      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  -- | gt      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  | le      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  -- | lt      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  -- | not     : Assert σ → Assert σ
  -- | and     : Assert σ → Assert σ → Assert σ
  -- | or      : Assert σ → Assert σ → Assert σ
  | implies : Assert σ → Assert σ → Assert σ

namespace Assert

-- Notation: `f =ₐ g`, `f ≤ₐ g` for atomic assertions and `A →ₐ B` for implication.
infix:50  " =ₐ " => eq
infix:50 " ≤ₐ " => le
infixr:25 " →ₐ " => implies

/-- Interpret an assertion `A` at a positive homomorphism `φ` as a `Prop`: atoms become
the corresponding `=`/`≤` on `φ`-values, implication becomes `→`. -/
def eval (A : Assert σ) (φ : PositiveHom σ) : Prop
  :=
  match A with
  -- | .false_ => False
  -- | .true_ => True
  | .eq f g => φ f = φ g
  -- | .ge f g => φ f ≥ φ g
  -- | .gt f g => φ f > φ g
  | .le f g => φ f ≤ φ g
  -- | .lt f g => φ f < φ g
  -- | .not A => ¬ A.eval φ
  -- | .and A B => A.eval φ ∧ B.eval φ
  -- | .or A B => A.eval φ ∨ B.eval φ
  | .implies A B => A.eval φ → B.eval φ

/-- An assertion is valid if it evaluates to `True` at every positive homomorphism. -/
def isValid (A : Assert σ) : Prop :=
  ∀ (φ : PositiveHom σ), A.eval φ

/-- `A` entails `B` when the implication `A →ₐ B` is valid. -/
def Entails (A B : Assert σ) : Prop :=
  isValid (A →ₐ B)

-- Notation: `A ⊢ₐ B` for `Entails A B`.
infix:20 " ⊢ₐ " => Entails

@[simp]
theorem eval_eq (f g : FlagAlgebra σ) (φ : PositiveHom σ)
    : (f =ₐ g).eval φ ↔ φ f = φ g :=
  Iff.rfl

@[simp]
theorem isValid_eq (f g : FlagAlgebra σ)
    : isValid (f =ₐ g) ↔ ∀ (φ : PositiveHom σ), φ f = φ g :=
  Iff.rfl

@[simp]
theorem entails_def (A B : Assert σ)
    : (A ⊢ₐ B) ↔ ∀ (φ : PositiveHom σ), A.eval φ → B.eval φ :=
  Iff.rfl

theorem eq_refl (f : FlagAlgebra σ) : isValid (f =ₐ f) := by
  intro φ
  rfl

theorem eq_symm (f g : FlagAlgebra σ)
    : isValid ((f =ₐ g) →ₐ (g =ₐ f)) := by
  intro φ hfg
  exact hfg.symm

theorem eq_trans (f g h : FlagAlgebra σ)
    : isValid ((f =ₐ g) →ₐ ((g =ₐ h) →ₐ (f =ₐ h))) := by
  intro φ hfg hgh
  exact Eq.trans hfg hgh

/-- `f ≡ₐ g`: the assertion `f =ₐ g` is valid, i.e. `φ f = φ g` for every positive
homomorphism `φ`. This is the DSL's equivalence relation on flag-algebra elements. -/
def Eqv (f g : FlagAlgebra σ) : Prop :=
  isValid (f =ₐ g)

-- Notation: `f ≡ₐ g` for `Eqv f g`.
infix:50 " ≡ₐ " => Eqv

@[simp]
theorem eqv_iff (f g : FlagAlgebra σ)
    : (f ≡ₐ g) ↔ ∀ (φ : PositiveHom σ), φ f = φ g :=
  Iff.rfl

theorem eqv_refl (f : FlagAlgebra σ) : f ≡ₐ f :=
  eq_refl f

theorem eqv_symm {f g : FlagAlgebra σ} (h : f ≡ₐ g) : g ≡ₐ f := by
  intro φ
  exact (h φ).symm

theorem eqv_trans {f g h : FlagAlgebra σ} (hfg : f ≡ₐ g) (hgh : g ≡ₐ h) : f ≡ₐ h := by
  intro φ
  exact Eq.trans (hfg φ) (hgh φ)

instance : Setoid (FlagAlgebra σ) where
  r := Eqv
  iseqv := ⟨eqv_refl, eqv_symm, eqv_trans⟩

theorem eqv_add {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
    : (f + g) ≡ₐ (f' + g') := by
  intro φ
  have hff' : φ f = φ f' := hf φ
  have hgg' : φ g = φ g' := hg φ
  calc
    φ (f + g) = φ f + φ g := PositiveHom.map_add φ f g
    _ = φ f' + φ g' := by rw [hff', hgg']
    _ = φ (f' + g') := (PositiveHom.map_add φ f' g').symm

theorem eqv_sub {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
    : (f - g) ≡ₐ (f' - g') := by
  intro φ
  have hff' : φ f = φ f' := hf φ
  have hgg' : φ g = φ g' := hg φ
  calc
    φ (f - g) = φ f - φ g := PositiveHom.map_sub φ f g
    _ = φ f' - φ g' := by rw [hff', hgg']
    _ = φ (f' - g') := (PositiveHom.map_sub φ f' g').symm

theorem eqv_mul {f f' g g' : FlagAlgebra σ} (hf : f ≡ₐ f') (hg : g ≡ₐ g')
    : (f * g) ≡ₐ (f' * g') := by
  intro φ
  have hff' : φ f = φ f' := hf φ
  have hgg' : φ g = φ g' := hg φ
  calc
    φ (f * g) = φ f * φ g := PositiveHom.map_mul φ f g
    _ = φ f' * φ g' := by rw [hff', hgg']
    _ = φ (f' * g') := (PositiveHom.map_mul φ f' g').symm

theorem eqv_smul (r : ℝ) {f g : FlagAlgebra σ} (hfg : f ≡ₐ g)
    : (r • f) ≡ₐ (r • g) := by
  intro φ
  have hfg' : φ f = φ g := hfg φ
  calc
    φ (r • f) = r * φ f := PositiveHom.map_smul φ r f
    _ = r * φ g := by rw [hfg']
    _ = φ (r • g) := (PositiveHom.map_smul φ r g).symm

@[simp]
theorem eval_le (f g : FlagAlgebra σ) (φ : PositiveHom σ)
    : (f ≤ₐ g).eval φ ↔ φ f ≤ φ g :=
  Iff.rfl

@[simp]
theorem isValid_le (f g : FlagAlgebra σ)
    : isValid (f ≤ₐ g) ↔ ∀ (φ : PositiveHom σ), φ f ≤ φ g :=
  Iff.rfl

@[simp]
theorem eval_implies (A B : Assert σ) (φ : PositiveHom σ)
    : (A →ₐ B).eval φ ↔ (A.eval φ → B.eval φ) :=
  Iff.rfl

@[simp]
theorem isValid_implies (A B : Assert σ)
    : isValid (A →ₐ B) ↔ ∀ (φ : PositiveHom σ), A.eval φ → B.eval φ :=
  Iff.rfl

theorem le_refl (f : FlagAlgebra σ) : isValid (f ≤ₐ f) := by
  intro φ
  exact le_rfl

theorem le_trans (f g h : FlagAlgebra σ)
    : isValid ((f ≤ₐ g) →ₐ ((g ≤ₐ h) →ₐ (f ≤ₐ h))) := by
  intro φ hfg hgh
  exact _root_.le_trans hfg hgh

theorem le_antisymm_eq (f g : FlagAlgebra σ)
    : isValid ((f ≤ₐ g) →ₐ ((g ≤ₐ f) →ₐ (f =ₐ g))) := by
  intro φ hfg hgf
  exact le_antisymm hfg hgf

theorem eq_implies_le (f g : FlagAlgebra σ)
    : isValid ((f =ₐ g) →ₐ (f ≤ₐ g)) := by
  intro φ hfg
  exact le_of_eq hfg

theorem eq_implies_le' (f g : FlagAlgebra σ)
    : isValid ((f =ₐ g) →ₐ (g ≤ₐ f)) := by
  intro φ hfg
  exact le_of_eq hfg.symm

theorem le_add_right (f g a : FlagAlgebra σ)
    : isValid ((f ≤ₐ g) →ₐ ((f + a) ≤ₐ (g + a))) := by
  intro φ hfg
  have hfg' : φ f + φ a ≤ φ g + φ a := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hfg (φ a)
  calc
    φ (f + a) = φ f + φ a := PositiveHom.map_add φ f a
    _ ≤ φ g + φ a := hfg'
    _ = φ (g + a) := (PositiveHom.map_add φ g a).symm

theorem le_add_left (f g a : FlagAlgebra σ)
    : isValid ((f ≤ₐ g) →ₐ ((a + f) ≤ₐ (a + g))) := by
  intro φ hfg
  have hfg' : φ a + φ f ≤ φ a + φ g := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hfg (φ a)
  calc
    φ (a + f) = φ a + φ f := PositiveHom.map_add φ a f
    _ ≤ φ a + φ g := hfg'
    _ = φ (a + g) := (PositiveHom.map_add φ a g).symm

theorem le_smul_nonneg (r : ℝ) (hr : 0 ≤ r) (f g : FlagAlgebra σ)
    : isValid ((f ≤ₐ g) →ₐ ((r • f) ≤ₐ (r • g))) := by
  intro φ hfg
  calc
    φ (r • f) = r * φ f := PositiveHom.map_smul φ r f
    _ ≤ r * φ g := mul_le_mul_of_nonneg_left hfg hr
    _ = φ (r • g) := (PositiveHom.map_smul φ r g).symm

theorem implies_refl (A : Assert σ) : isValid (A →ₐ A) := by
  intro φ hA
  exact hA

theorem implies_trans (A B C : Assert σ)
    : isValid ((A →ₐ B) →ₐ ((B →ₐ C) →ₐ (A →ₐ C))) := by
  intro φ hAB hBC hA
  exact hBC (hAB hA)

theorem modus_ponens {A B : Assert σ}
    (hA : isValid A) (hAB : isValid (A →ₐ B))
    : isValid B := by
  intro φ
  exact hAB φ (hA φ)

theorem entails_refl (A : Assert σ) : A ⊢ₐ A :=
  implies_refl A

theorem entails_trans {A B C : Assert σ} (hAB : A ⊢ₐ B) (hBC : B ⊢ₐ C) : A ⊢ₐ C := by
  intro φ hA
  exact hBC φ (hAB φ hA)

attribute [refl] eqv_refl
attribute [symm] eqv_symm
attribute [trans] eqv_trans
attribute [refl] entails_refl
attribute [trans] entails_trans

@[simp]
theorem eqv_iff_isValid_eq (f g : FlagAlgebra σ) : (f ≡ₐ g) ↔ isValid (f =ₐ g) :=
  Iff.rfl

@[simp]
theorem entails_iff_isValid_implies (A B : Assert σ) : (A ⊢ₐ B) ↔ isValid (A →ₐ B) :=
  Iff.rfl

theorem eqv_of_valid_eq {f g : FlagAlgebra σ} (h : isValid (f =ₐ g)) : f ≡ₐ g :=
  h

theorem valid_eq_of_eqv {f g : FlagAlgebra σ} (h : f ≡ₐ g) : isValid (f =ₐ g) :=
  h

theorem entails_of_isValid {A B : Assert σ} (hB : isValid B) : A ⊢ₐ B := by
  intro φ _
  exact hB φ

theorem isValid_of_entails {A B : Assert σ} (hAB : A ⊢ₐ B) (hA : isValid A) : isValid B := by
  intro φ
  exact hAB φ (hA φ)

theorem entails_mp {A B : Assert σ} (hAB : A ⊢ₐ B) (hA : isValid A) : isValid B :=
  isValid_of_entails hAB hA

theorem entails_eq_subst_right {f g h : FlagAlgebra σ} (hfg : f ≡ₐ g) : (f ≡ₐ h) ↔ (g ≡ₐ h) := by
  constructor
  · intro hfh
    exact eqv_trans (eqv_symm hfg) hfh
  · intro hgh
    exact eqv_trans hfg hgh

theorem entails_eq_subst_left {f g h : FlagAlgebra σ} (hfg : f ≡ₐ g) : (h ≡ₐ f) ↔ (h ≡ₐ g) := by
  constructor
  · intro hhf
    exact eqv_trans hhf hfg
  · intro hhg
    exact eqv_trans hhg (eqv_symm hfg)

end Assert

end FlagLogic
