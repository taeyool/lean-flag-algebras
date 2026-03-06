import LeanFlagAlgebras.Logic.Defs

open FlagAlgebras

namespace FlagLogic

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

namespace Assert

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
