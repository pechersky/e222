import data.matrix.basic
import algebra.invertible

variables (n : Type*) [fintype n] [decidable_eq n] (R : Type*) [field R]

section invertible

variables (n)
-- ... Invertible matrices make sense only on spaces that are one-dimensional or larger
def invertible_matrix := { A : matrix n n R // ∃ (B : matrix n n R), A * B = 1 ∧ B * A = 1 }
variables {n} {R}

-- ... let's motivate the uniqueness usage by proving uniqueness
lemma inv_mat_unique {A B C : matrix n n R} (hB : A * B = 1) (hC : C * A = 1) : B = C :=
by rw [<-one_mul B, <-hC, mul_assoc, hB, mul_one]

section coe
variables (A B : invertible_matrix n R)

instance coe_matrix : has_coe (invertible_matrix n R) (matrix n n R) :=
by delta invertible_matrix; apply_instance

@[simp] lemma coe_invertible_eq_self {A : invertible_matrix n R} : ↑A = A.val := rfl

instance coe_fun : has_coe_to_fun (invertible_matrix n R) :=
⟨λ _, n -> n -> R, λ A, A.val⟩

@[simp] lemma coe_invertible_fun_eq_self {A : invertible_matrix n R} : ⇑A = A.val := rfl

lemma inv_ext_iff : A = B ↔ (∀ i j, A i j = B i j) :=
iff.trans subtype.ext ⟨λ h i j, congr_fun (congr_fun h i) j, matrix.ext⟩

@[ext] lemma inv_ext : (∀ i j, A i j = B i j) -> A = B :=
(inv_ext_iff A B).mpr

-- ... proving an existence of an inverse is noncomputable
-- ... because we do not construct it
noncomputable def inv_mat : matrix n n R :=
classical.some A.property

@[simp] lemma inv_mat_cancel_self : inv_mat A * A.val = 1 :=
(classical.some_spec A.property).2

@[simp] lemma inv_mat_cancel_self' : inv_mat A * ↑A = 1 :=
(classical.some_spec A.property).2

@[simp] lemma inv_mat_cancel_self'' : inv_mat A * ⇑A = 1 :=
(classical.some_spec A.property).2

@[simp] lemma mat_cancel_inv_self : A.val * inv_mat A = 1 :=
(classical.some_spec A.property).1

@[simp] lemma mat_cancel_inv_self' : ↑A * inv_mat A = 1 :=
(classical.some_spec A.property).1

end coe

section inv_instances
variables (A B : invertible_matrix n R)

lemma inv_mat_has_inv :
  ∃ (B : matrix n n R), inv_mat A * B = 1 ∧ B * inv_mat A = 1 :=
begin
  use A.val,
  split,
  { exact inv_mat_cancel_self _ },
  { exact mat_cancel_inv_self _ }
end

-- noncomputable instance inv_mat_inv : has_inv (invertible_matrix n R) := ⟨inv_mat⟩
noncomputable instance inv_mat_inv : has_inv (invertible_matrix n R) :=
⟨λ A, ⟨inv_mat A, inv_mat_has_inv _⟩⟩

lemma inv_mat_mul_has_inv  :
  ∃ (C : matrix n n R), (A.val * ↑B) * C = 1 ∧ C * (↑A * ↑B) = 1 :=
begin
  obtain ⟨Ainv, hA⟩ := A.property,
  obtain ⟨Binv, hB⟩ := B.property,
  use Binv * Ainv,
  dsimp only [coe_invertible_eq_self] at *,
  split,
  { rw [mul_assoc, <-mul_assoc _ Binv, hB.1, one_mul, hA.1] },
  { rw [mul_assoc, <-mul_assoc Ainv, hA.2, one_mul, hB.2] } 
end

instance inv_mat_mul : has_mul (invertible_matrix n R) :=
⟨λ A B, ⟨A.val * B.val, inv_mat_mul_has_inv _ _⟩⟩

instance inv_mat_one : has_one (invertible_matrix n R) :=
⟨⟨1, by {use 1, simp}⟩⟩

@[simp] lemma inv_mat_val : ↑(A⁻¹) = inv_mat A := rfl
@[simp] lemma inv_mat_val' : (A⁻¹).val = inv_mat A := rfl
@[simp] lemma inv_mat_apply : ⇑(A⁻¹) = inv_mat A := rfl

@[simp] lemma inv_mat_mul_val : ↑(A * B) = matrix.mul A.val B.val := rfl
@[simp] lemma inv_mat_mul_val' : (A * B).val = matrix.mul A.val B.val := rfl
@[simp] lemma inv_mat_mul_apply : ⇑(A * B) = matrix.mul A.val B.val := rfl

@[simp] lemma inv_mat_one_val : ↑(1 : invertible_matrix n R) = (1 : matrix n n R) := rfl
@[simp] lemma inv_mat_one_val' : (1 : invertible_matrix n R).val = (1 : matrix n n R) := rfl
@[simp] lemma inv_mat_one_apply : ⇑(1 : invertible_matrix n R) = (1 : matrix n n R) := rfl

end inv_instances

section cancel
variables (A : invertible_matrix n R)
variables (B C : matrix n n R)

@[simp] lemma mat_inv_eq_inv_mat : A⁻¹.val = inv_mat A := rfl

@[simp] lemma mat_inv_right_cancel_self : A * A⁻¹ = 1 :=
by { refine subtype.eq _, rw [inv_mat_mul_val', inv_mat_val'], exact mat_cancel_inv_self _, }

@[simp] lemma mat_inv_val_right_cancel_self : A.val * A⁻¹.val = 1 :=
by simp

@[simp] lemma mat_inv_left_cancel_self : A⁻¹ * A = 1 :=
by { refine subtype.eq _, rw [inv_mat_mul_val', inv_mat_val'], exact inv_mat_cancel_self _, }

@[simp] lemma mat_inv_val_left_cancel_self : A⁻¹.val * A.val = 1 :=
by simp

@[simp] lemma mat_inv_left_cancel : ↑A * ↑A⁻¹ * B = B :=
by simp

@[simp] lemma mat_inv_right_cancel : B * ↑A * ↑A⁻¹ = B :=
by simp [mul_assoc, -matrix.mul_eq_mul] 

@[simp] lemma inv_mat_left_cancel : ↑A⁻¹ * ↑A * B = B :=
by simp

@[simp] lemma inv_mat_right_cancel : B * ↑A⁻¹ * ↑A = B :=
by simp [mul_assoc, -matrix.mul_eq_mul] 

@[simp] lemma mat_mul_right_inj : ↑A * B = ↑A * C ↔ B = C :=
begin
  split,
  { intros H,
    replace H := congr_arg ((*) ↑A⁻¹) H,
    repeat { rwa [<-mul_assoc, inv_mat_left_cancel] at H }, },
  { exact congr_arg _} 
end

@[simp] lemma mat_mul_left_inj : B * ↑A = C * ↑A ↔ B = C :=
begin
  split,
  { intros H,
    replace H := congr_arg (λ M, M * ↑A⁻¹) H,
    dsimp only [] at H,
    repeat { rwa [mat_inv_right_cancel] at H } },
  { exact congr_arg _} 
end

end cancel

lemma inv_mat_nonzero (n : ℕ) (npos : 0 < n) (A : invertible_matrix (fin n) R) : A.val ≠ 0 :=
begin
  obtain ⟨B, hB⟩ := A.property,
  intros H,
  rw [H, zero_mul] at hB,
  have z : fin n := ⟨0, npos⟩,
  replace hB := congr_fun (congr_fun hB.left z) z,
  norm_num at hB,
  exact hB
end

variables (n)
noncomputable instance inv_matrix (A : invertible_matrix n R) : invertible A :=
{
  inv_of := A⁻¹,
  inv_of_mul_self := mat_inv_left_cancel_self A,
  mul_inv_of_self := mat_inv_right_cancel_self A, 
}

variables {n}

end invertible

example (A B : invertible_matrix (fin 1) R) (z : fin 1) :
        A.val ≠ 0 ∧ B z z = 1 / (A z z) ↔ A⁻¹ = B :=
begin
  have hz : default (fin 1) = z,
    from subsingleton.elim _ _,
  have nonzeroA : A.val ≠ 0,
    from inv_mat_nonzero _ (by linarith) _,
  have nonzero : A z z ≠ 0,
    { intros nz,
      refine nonzeroA _,
      ext i j,
      rw [matrix.zero_val, subsingleton.elim i z, subsingleton.elim j z,
          <-coe_invertible_fun_eq_self],
      simp [nz] },
  have hinv: A⁻¹ * A = 1,
    from inv_of_mul_self A, 
  have valinv : A⁻¹ z z = (A z z)⁻¹,
    { rw inv_ext_iff at hinv,
      specialize hinv z z,
      rw [inv_mat_mul_apply, matrix.mul_val] at hinv,
      rw [inv_eq_one_div, (div_eq_iff_mul_eq nonzero).mpr],
      simp [*, hz] at *},
  split,
  { rintros ⟨hA, hB⟩,
    rw [one_div_eq_inv] at hB,
    ext i j,
    rw [subsingleton.elim i z, subsingleton.elim j z, hB, valinv] },
  { intro h,
    split,
    { exact nonzeroA },
    { refine (eq_div_iff nonzero).mpr _,
      rw inv_ext_iff at h,
      specialize h z z,
      rw [<-h, valinv, inv_mul_cancel nonzero] } }
end