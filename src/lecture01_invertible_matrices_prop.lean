import data.matrix.notation
import algebra.invertible
import tactic

open_locale matrix

variables (n : ℕ) (R : Type*) [field R]

section invertible
variables (A B C D : matrix (fin n) (fin n) R)
variables {n} {R}

@[reducible] def mat_invertible : Prop := A * B = 1 ∧ B * A = 1

lemma inv_mat_unique (hB : mat_invertible A B) (hC : mat_invertible A C) : B = C :=
by rw [<-one_mul B, <-hC.right, mul_assoc, hB.left, mul_one]

@[simp] lemma mat_invertible_iff : mat_invertible A B ↔ A * B = 1 ∧ B * A = 1 := iff.rfl

@[simp] lemma mat_invertible_inv : mat_invertible A B ↔ mat_invertible B A :=
by split; intros h; simp * at *

section cancel

-- ... not simp to prevent deep stack
lemma mat_inv_right_cancel_self (h : mat_invertible A B) : A * B = 1 :=
h.left

-- ... not simp to prevent deep stack
lemma mat_inv_left_cancel_self (h : mat_invertible A B) : B * A = 1 :=
h.right

@[simp] lemma mat_inv_left_cancel (h : mat_invertible A B) : A * B * C = C :=
by { rw [h.left, one_mul] }

@[simp] lemma mat_inv_right_cancel (h : mat_invertible A B) : C * A * B = C :=
by { rw [mul_assoc, h.left, mul_one] }

@[simp] lemma inv_mat_left_cancel (h : mat_invertible A B) : B * A * C = C :=
by { rw [h.right, one_mul] }

@[simp] lemma inv_mat_right_cancel (h : mat_invertible A B) : C * B * A = C :=
by { rw [mul_assoc, h.right, mul_one] }

@[simp] lemma mat_mul_right_inj (h : mat_invertible A B) : A * C = A * D ↔ C = D :=
begin
  split,
  { intros H,
    replace H := congr_arg ((*) B) H,
    repeat { rwa [<-mul_assoc, inv_mat_left_cancel _ _ _ h] at H } },
  { exact congr_arg _}
end

@[simp] lemma mat_mul_left_inj (h : mat_invertible A B) : C * A = D * A ↔ C = D :=
begin
  split,
  { intros H,
    replace H := congr_arg (λ M, M * B) H,
    dsimp only [] at H,
    repeat { rwa [mat_inv_right_cancel _ _ _ h] at H } },
  { exact congr_arg _}
end

lemma inv_mat_nonzero (npos : 0 < n) (h : mat_invertible A B) : A ≠ 0 :=
begin
  intros hA,
  let z : (fin n) := ⟨0, npos⟩,
  replace h := congr_fun (congr_fun h.left z) z,
  rw hA at h,
  norm_num at h,
  exact h
end

end cancel

lemma inv_mat_one (n : ℕ) : mat_invertible (1 : matrix (fin n) (fin n) R) 1 := by simp

variables (n)
instance inv_matrix (h : mat_invertible A B) : invertible A :=
{
  inv_of := B,
  inv_of_mul_self := h.right,
  mul_inv_of_self := h.left,
}
variables {n}

end invertible

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
      from inv_mat_nonzero _ _ (by linarith) h,
    split,
    { exact nonzeroA },
    { refine (eq_div_iff (nonzero nonzeroA)).mpr _,
      replace h := congr_fun (congr_fun h.right z) z,
      rw [matrix.mul_eq_mul, matrix.mul_val] at h,
      simp * at * } }
end

-- universe u
-- variables {α : Type u} [semiring α]
-- variables {m o : ℕ} {m' n' o' : Type} [fintype m'] [fintype n']
-- @[simp] lemma smul_cons_cons (x : α) (v : n' → α) (A : matrix (fin m) n' α) :
--   x • matrix.vec_cons v A = matrix.vec_cons (x • v) (x • A) :=
-- by { ext i, refine fin.cases _ _ i; simp }

-- @[simp] lemma smul_empty' (x : α) : x • @matrix.vec_empty (m' → α) = matrix.vec_empty :=
-- by { ext i, fin_cases i }

-- @[simp] lemma mul_val_succ' (A : matrix m' n' α) (B : matrix n' (fin o.succ) α) (i : m') (j : fin o) :
--   (A ⬝ B) i j.succ = (A ⬝ matrix.vec_tail ∘ B) i j := rfl

lemma mul_cons {m n o : ℕ} {α : Type*} [comm_semiring α]
  (A : matrix (fin m.succ) (fin n.succ) α) (B : matrix (fin n.succ) (fin o.succ) α) :
  A ⬝ B = (matrix.vec_cons (matrix.mul_vec A (matrix.vec_head Bᵀ)) (A ⬝ (matrix.vec_tail Bᵀ)ᵀ)ᵀ)ᵀ :=
-- by { ext i j, refine fin.cases _ _ i, { simp, refine fin.cases _ _ j, refl, simp, }, simp [mul_val_succ] }
begin
  ext i j,
  refine fin.cases _ _ i;
  induction j with kj hkj;
  induction kj with nj hnj;
  { intros, simp, refl },
end

example (A : matrix (fin 2) (fin 2) R) {a b c d : R} (hA : A = ![![a, b], ![c, d]]) :
        a * d - b * c ≠ 0 ↔ ∃ B, mat_invertible A B :=
begin
  split,
  { intros h,
    use (1 / (a * d - b * c)) • ![![d, -b], ![-c, a]],
    split;
      { ext i j,
        fin_cases i;
        fin_cases j;
        field_simp [hA, h];
        ring } },
  { intros h H,
    rcases h with ⟨B, hAB, hBA⟩,
    rw [<-matrix.ext_iff, hA, matrix.mul_eq_mul] at hBA,
    simp [mul_cons, matrix.vec_head, matrix.vec_tail] at hBA,
    let hBA' := hBA 0 0,
    let hBA'''' := hBA 0 1,
    let hBA''' := hBA 1 0,
    let hBA'' := hBA 1 1,
    have finne : ((0 : fin 2) ≠ 1) := fin.ne_of_vne zero_ne_one,
    simp [finne] at hBA' hBA'' hBA''' hBA'''',
    classical,
    by_cases ha : a = 0;
    by_cases hb : b = 0;
    by_cases hc : c = 0;
    by_cases hd : d = 0,
    -- at least one element of A is zero
    any_goals
      { simp [ha, hb, hc, hd, mul_zero, sub_zero, mul_eq_zero] at H,
        cases H;
        simp * at * },
    -- all elements of A nonzero
    { have ha' : a = b * c / d,
        by { rw eq_div_iff hd, rw <-sub_eq_zero, exact H },
      change (a * B 0 0 + c * B 0 1 = 1) at hBA',
      change (b * B 0 0 + d * B 0 1 = 0) at hBA'''',
      have hBv : B 0 1 = - b / d * B 0 0,
        { field_simp [hb, hd],
          rw <-eq_neg_iff_add_eq_zero at hBA'''',
          simp [hBA'''', mul_comm] },
      have hd' : d = 0,
        { field_simp [ha', ha, hb, hc, hd, hBv] at hBA',
          rw <-hBA',
          ring },
      exact absurd hd' hd } }
end
