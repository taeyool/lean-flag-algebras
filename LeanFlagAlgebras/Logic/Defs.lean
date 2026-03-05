import LeanFlagAlgebras.FlagAlgebra.PositiveHom

open FlagAlgebras

namespace FlagLogic

variable {n₀ : ℕ} {σ : FlagType (Fin n₀)}

inductive Assert (σ : FlagType (Fin n₀)) where
  | false_  : Assert σ
  | true_   : Assert σ
  | eq      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  | ge      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  | gt      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  | le      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  | lt      : FlagAlgebra σ → FlagAlgebra σ → Assert σ
  | not     : Assert σ → Assert σ
  | and     : Assert σ → Assert σ → Assert σ
  | or      : Assert σ → Assert σ → Assert σ
  | implies : Assert σ → Assert σ → Assert σ

namespace Assert

-- infix:50 " ≥_f " => ge
-- infixr:35 " ∧_f " => and
-- infixr:30 " ∨_f " => or
-- infixr:25 " ⇒_f " => implies
-- infix:50  " =_f " => eq

def eval (A : Assert σ) (φ : PositiveHom σ) : Prop
  :=
  match A with
  | .false_ => False
  | .true_ => True
  | .eq f g => φ f = φ g
  | .ge f g => φ f ≥ φ g
  | .gt f g => φ f > φ g
  | .le f g => φ f ≤ φ g
  | .lt f g => φ f < φ g
  | .not A => ¬ A.eval φ
  | .and A B => A.eval φ ∧ B.eval φ
  | .or A B => A.eval φ ∨ B.eval φ
  | .implies A B => A.eval φ → B.eval φ

def isValid (A : Assert σ) : Prop :=
  ∀ (φ : PositiveHom σ), A.eval φ

end Assert

end FlagLogic
