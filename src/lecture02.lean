import lecture01
import data.complex.basic

namespace e222

variables {n : ℕ}

example : GLₙ n ℝ = units (matrix (fin n) (fin n) ℝ) := rfl
example : GLₙ n ℂ = units (matrix (fin n) (fin n) ℂ) := rfl
example : GLₙ n ℚ = units (matrix (fin n) (fin n) ℚ) := rfl

variables {G : Type*} [group G] (a b c : G)

example : a * (b * c) = a * b * c := group.mul_assoc _ _ _
example : 1 * a = a ∧ a * 1 = a := ⟨group.one_mul _, group.mul_one _⟩
example : a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 := ⟨group.mul_inv _, group.inv_mul _⟩

noncomputable instance {K n' : Type*} [comm_ring K] [fintype n'] [decidable_eq n'] :
  group (units (matrix n' n' K)) :=
{ op := (*),
  assoc' := λ _ _ _, units.ext $
    by simp only [units.coe_mul, matrix.mul_eq_mul, ←matrix.mul_assoc],
  e := 1,
  op_e' := λ _, units.ext $ by
    by simp only [units.coe_mul, units.coe_one, matrix.mul_eq_mul, matrix.mul_one],
  e_op' := λ _, units.ext $ by
    by simp only [units.coe_mul, units.coe_one, matrix.mul_eq_mul, matrix.one_mul],
  inv := λ a, ⟨a⁻¹, a,
    by rw [matrix.mul_eq_mul, matrix.nonsing_inv_mul _
           ((matrix.is_unit_iff_is_unit_det _).mp (is_unit_unit a))],
    by rw [matrix.mul_eq_mul, matrix.mul_nonsing_inv _
           ((matrix.is_unit_iff_is_unit_det _).mp (is_unit_unit a))]⟩,
  inv_op' := λ _, units.ext $ by
    rw [units.coe_mul, units.coe_mk, units.coe_one,
        matrix.mul_eq_mul, matrix.nonsing_inv_mul _
        ((matrix.is_unit_iff_is_unit_det _).mp (is_unit_unit _))],
  op_inv' := λ _, units.ext $ by
    rw [units.coe_mul, units.coe_mk, units.coe_one,
        matrix.mul_eq_mul, matrix.mul_nonsing_inv _
        ((matrix.is_unit_iff_is_unit_det _).mp (is_unit_unit _))] }

noncomputable instance : group (GLₙ n ℝ) := by apply_instance

instance (T : Type*) : group (T ≃ T) :=
{ op := equiv.trans,
  assoc' := equiv.trans_assoc,
  e := equiv.refl _,
  op_e' := equiv.trans_refl,
  e_op' := equiv.refl_trans,
  inv := equiv.symm,
  inv_op' := equiv.symm_trans,
  op_inv' := equiv.trans_symm }

end e222
