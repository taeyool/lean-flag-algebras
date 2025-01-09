import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs

/-- Alternative structure for real numbers -/
structure Real' where
  val : ℝ  -- underlying real value

instance : Coe Real' ℝ where
  coe x := x.val

instance : Add Real' where
  add x y := ⟨x.val + y.val⟩

instance : Mul Real' where
  mul r1 r2 := ⟨r1.val * r2.val⟩

instance : Zero Real' where
  zero := ⟨0⟩

instance : One Real' where
  one := ⟨1⟩

instance : Neg Real' where
  neg r := ⟨-r.val⟩

instance : Ring Real' where
  add := (· + ·)
  add_assoc := by
    intro a b c
    exact congrArg Real'.mk (add_assoc a.val b.val c.val)
  zero := 0
  zero_add := by
    intro a
    exact congrArg Real'.mk (zero_add a.val)
  add_zero := by
    intro a
    exact congrArg Real'.mk (add_zero a.val)
  neg := -(·)
  add_comm := by
    intro a b
    exact congrArg Real'.mk (add_comm a.val b.val)
  neg_add_cancel := by
    intro a
    exact congrArg Real'.mk (neg_add_cancel a.val)
  mul := (· * ·)
  mul_assoc := by
    intro a b c
    exact congrArg Real'.mk (mul_assoc a.val b.val c.val)
  zero_mul := by
    intro a
    exact congrArg Real'.mk (zero_mul a.val)
  mul_zero := by
    intro a
    exact congrArg Real'.mk (mul_zero a.val)
  one := 1
  one_mul := by
    intro a
    exact congrArg Real'.mk (one_mul a.val)
  mul_one := by
    intro a
    exact congrArg Real'.mk (mul_one a.val)
  left_distrib := by
    intro a b c
    refine congrArg Real'.mk ?_
    exact left_distrib a.val b.val c.val
  right_distrib := by
    intro a b c
    refine congrArg Real'.mk ?_
    exact right_distrib a.val b.val c.val
  nsmul n x := ⟨n • x.val⟩
  nsmul_zero := by
    intro x
    simp; rfl
  nsmul_succ := by
    intro n x
    simp [add_one_mul]
    rfl
  zsmul n x := ⟨n • x.val⟩

instance : CommRing Real' where
  mul_comm := by
    intro a b
    exact congrArg Real'.mk (mul_comm a.val b.val)

instance : Algebra ℝ Real' where
  smul r x := ⟨r * x.val⟩
  toFun r := ⟨r⟩
  map_zero' := by simp; rfl
  map_one' := by simp; rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  smul_def' := by intros; rfl
  commutes' := by
    intro x y
    simp
    calc
      _ = { val := x * y.val } := rfl
      _ = { val := y.val * x } := by rw [mul_comm]
      _ = y * { val := x } := rfl
