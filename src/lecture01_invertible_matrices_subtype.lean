import data.matrix.basic
import linear_algebra.matrix
import algebra.invertible

open_locale classical

variables (n : Type*) [fintype n] [decidable_eq n] (R : Type*) [field R]

section invertible

variables (n)
-- ... Invertible matrices make sense only on spaces that are one-dimensional or larger
def invertible_matrix := { A : matrix n n R // ∃! (B : matrix n n R), A * B = 1 ∧ B * A = 1 }
variables {n} {R}

-- ... let's motivate the uniqueness usage by proving uniqueness
lemma inv_mat_unique {A B C : matrix n n R} (hB : A * B = 1) (hC : C * A = 1) : B = C :=
by rw [<-one_mul B, <-hC, mul_assoc, hB, mul_one]

instance coe_matrix : has_coe (invertible_matrix n R) (matrix n n R) :=
by delta invertible_matrix; apply_instance

@[simp] lemma coe_invertible_eq_self {A : invertible_matrix n R} : ↑A = A.val := rfl

instance coe_fun : has_coe_to_fun (invertible_matrix n R) :=
⟨λ _, n -> n -> R, λ A, A.val⟩

lemma inv_ext_iff (A B : invertible_matrix n R) : A = B ↔ (∀ i j, A i j = B i j) :=
iff.trans subtype.ext ⟨λ h i j, congr_fun (congr_fun h i) j, matrix.ext⟩

@[ext] lemma inv_ext (A B : invertible_matrix n R) : (∀ i j, A i j = B i j) -> A = B :=
(inv_ext_iff A B).mpr

-- ... proving an existence of an inverse is noncomputable
-- ... because we do not construct it
noncomputable def inv_mat (A : invertible_matrix n R) : matrix n n R :=
classical.some A.property

@[simp] lemma inv_mat_cancel_self (A : invertible_matrix n R) : inv_mat A * A = 1 :=
(classical.some_spec A.property).1.2

@[simp] lemma mat_cancel_inv_self (A : invertible_matrix n R) : ↑A * inv_mat A = 1 :=
(classical.some_spec A.property).1.1

lemma inv_mat_has_inv (A : invertible_matrix n R) :
  ∃! (B : matrix n n R), inv_mat A * B = 1 ∧ B * inv_mat A = 1 :=
begin
  use A.val,
  split,
  { split,
    { exact inv_mat_cancel_self _ },
    { exact mat_cancel_inv_self _ } },
  { rintros a' ⟨hleft', hright'⟩,
    refine inv_mat_unique hleft' _,
    exact mat_cancel_inv_self _ }
end

-- noncomputable instance inv_mat_inv : has_inv (invertible_matrix n R) := ⟨inv_mat⟩
noncomputable instance inv_mat_inv : has_inv (invertible_matrix n R) :=
⟨λ A, ⟨inv_mat A, inv_mat_has_inv _⟩⟩

lemma inv_mat_mul_has_inv (A B : invertible_matrix n R) :
  ∃! (C : matrix n n R), (A.val * ↑B) * C = 1 ∧ C * (↑A * ↑B) = 1 :=
begin
  obtain ⟨Ainv, hA, hAuniq⟩ := A.property,
  obtain ⟨Binv, hB, hBuniq⟩ := B.property,
  use Binv * Ainv,
  dsimp only [coe_invertible_eq_self] at *,
  split,
  { split,
    { rw [mul_assoc, <-mul_assoc _ Binv, hB.1, one_mul, hA.1] },
    { rw [mul_assoc, <-mul_assoc Ainv, hA.2, one_mul, hB.2] } },
  { intros C hC,
    refine inv_mat_unique hC.left _,
    rw [mul_assoc, <-mul_assoc Ainv, hA.2, one_mul, hB.2]} 
end

instance inv_mat_mul : has_mul (invertible_matrix n R) :=
⟨λ A B, ⟨A.val * B.val, inv_mat_mul_has_inv _ _⟩⟩

instance inv_mat_one : has_one (invertible_matrix n R) :=
⟨⟨1, by {use 1, simp}⟩⟩

lemma inv_mat_nonzero (n : ℕ) (npos : 0 < n) (A : invertible_matrix (fin n) R) : A.val ≠ 0 :=
begin
  obtain ⟨B, hB, huniq⟩ := A.property,
  intros H,
  rw [H, zero_mul] at hB,
  have z : fin n := ⟨0, npos⟩,
  replace hB := congr_fun (congr_fun hB.left z) z,
  norm_num at hB,
  exact hB
end

@[simp] lemma inv_mat_val (A : invertible_matrix n R) : ↑(A⁻¹) = inv_mat A := rfl
@[simp] lemma inv_mat_val' (A : invertible_matrix n R) : (A⁻¹).val = inv_mat A := rfl
@[simp] lemma inv_mat_apply (A : invertible_matrix n R) : ⇑(A⁻¹) = inv_mat A := rfl

@[simp] lemma inv_mat_mul_val (A B : invertible_matrix n R) : ↑(A * B) = matrix.mul A.val B.val := rfl
@[simp] lemma inv_mat_mul_val' (A B : invertible_matrix n R) : (A * B).val = matrix.mul A.val B.val := rfl
@[simp] lemma inv_mat_mul_apply (A B : invertible_matrix n R) : ⇑(A * B) = matrix.mul A.val B.val := rfl

@[simp] lemma inv_mat_one_val : ↑(1 : invertible_matrix n R) = (1 : matrix n n R) := rfl
@[simp] lemma inv_mat_one_val' : (1 : invertible_matrix n R).val = (1 : matrix n n R) := rfl
@[simp] lemma inv_mat_one_apply : ⇑(1 : invertible_matrix n R) = (1 : matrix n n R) := rfl

variables (n)
noncomputable instance inv_matrix (A : invertible_matrix n R) : invertible A :=
{
  inv_of := A⁻¹,
  inv_of_mul_self := by { refine subtype.eq _,
                          rw [inv_mat_mul_val', inv_mat_val'],
                          exact inv_mat_cancel_self _, } ,
  mul_inv_of_self := by { refine subtype.eq _,
                          rw [inv_mat_mul_val', inv_mat_val'],
                          exact mat_cancel_inv_self _, }
}

variables {n}

end invertible