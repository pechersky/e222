import data.matrix.basic
import algebra.invertible

variables (n : ℕ) (R : Type*) [field R]
variables (A B C D : matrix (fin n) (fin n) R)

variables {n} {R} 
-- attempt using (*)
@[reducible] def mat_invertible : Prop := A * B = 1 ∧ B * A = 1

@[simp] lemma mat_invertible_def : mat_invertible A B ↔ A * B = 1 ∧ B * A = 1 := iff.rfl

@[simp] lemma mat_invertible_inv : mat_invertible A B ↔ mat_invertible B A :=
by split; intros h; simp * at *

@[simp] lemma mat_inv_left_cancel (h : mat_invertible A B) : A * B * C = C :=
by simp * at *

@[simp] lemma mat_inv_right_cancel (h : mat_invertible A B) : C * A * B = C :=
by simp [*, matrix.mul_assoc] at *

@[simp] lemma inv_mat_left_cancel (h : mat_invertible A B) : B * A * C = C :=
by simp * at *

@[simp] lemma inv_mat_right_cancel (h : mat_invertible A B) : C * A * B = C :=
by simp [*, matrix.mul_assoc] at *

@[simp] lemma mat_mul_right_inj (h : mat_invertible A B) : A * C = A * D ↔ C = D :=
begin
  split,
  { intros H,
    replace H := congr_arg ((*) B) H,
    repeat {rwa [<-mul_assoc, inv_mat_left_cancel _ _ _ h] at H} },
  { exact congr_arg _} 
end

@[simp] lemma mat_mul_left_inj (h : mat_invertible A B) : C * A = D * A ↔ C = D :=
begin
  split,
  { intros H,
    replace H := congr_arg (λ M, M * B) H,
    dsimp only [] at H,
    repeat {rwa [inv_mat_right_cancel _ _ _ h] at H} },
  { exact congr_arg _} 
end

lemma mat_inv_neq_zero (npos : 0 < n) (h : mat_invertible A B) : A ≠ 0 :=
begin
  intros hA,
  let z : (fin n) := ⟨0, npos⟩,
  replace h := congr_fun (congr_fun h.left z) z,
  rw hA at h,
  norm_num at h,
  exact h
end

lemma mat_inv_one_self (n : ℕ) : mat_invertible (1 : matrix (fin n) (fin n) R) 1 := by simp

lemma inv_mat_unique (hB : mat_invertible A B) (hC : mat_invertible A C) : B = C :=
by { rw <-mat_mul_right_inj _ _ _ _ hB, simp * at * }

variables (n)
instance inv_matrix (h : mat_invertible A B) : invertible A :=
{
  inv_of := B,
  inv_of_mul_self := h.right,
  mul_inv_of_self := h.left,
}
variables {n}

example (A B : matrix (fin 1) (fin 1) R) (z : fin 1) :
        A ≠ 0 ∧ B z z = 1 / (A z z) ↔ mat_invertible A B :=
begin
  have hz : default (fin 1) = z,
    from subsingleton.elim _ _,
  have nonzero : A ≠ 0 -> A z z ≠ 0,
    { intros nonzeroA nz,
      refine nonzeroA _,
      ext i j,
      simp [subsingleton.elim i z, subsingleton.elim j z, nz] },
  split,
  { rintros ⟨hA, hB⟩,
    split;
    { ext i j,
      rw [matrix.mul_eq_mul, matrix.mul_val,
          subsingleton.elim i z, subsingleton.elim j z],
      simp [nonzero hA, hB, hz] } },
  { intro h,
    have nonzeroA : A ≠ 0,
      from mat_inv_neq_zero _ _ (by linarith) h,
    split,
    { exact nonzeroA },
    { refine (eq_div_iff (nonzero nonzeroA)).mpr _,
      replace h := congr_fun (congr_fun h.right z) z,
      rw [matrix.mul_eq_mul, matrix.mul_val] at h,
      simp * at * } }
end