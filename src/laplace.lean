import data.matrix.notation
import data.nat.basic
import tactic.ring
import tactic.linarith

open_locale big_operators

universe u
variables {R : Type*} [field R]
variables {n m : ℕ}

open matrix

section bit

@[simp] lemma bit0_val {n : ℕ} : ∀ k : fin n, (bit0 k).val = bit0 (k.val) % n
| ⟨_, _⟩ := rfl

@[simp] lemma bit1_val {n : ℕ} (k : fin (n + 1)) : (bit1 k).val = (bit1 (k.val)) % (n + 1) :=
by simp [bit1, bit0, fin.add_def, fin.one_val]

end bit

section succ

@[simp] lemma succ_above_below {n : ℕ} (p : fin (n + 1)) (i : fin n) (h : i.val < p.val) : p.succ_above i = i.cast_succ :=
by { rw [fin.succ_above], split_ifs, refl }

@[simp] lemma succ_above_above {n : ℕ} (p : fin (n + 1)) (i : fin n) (h : p.val ≤ i.val) : p.succ_above i = i.succ :=
by { rw [fin.succ_above], split_ifs, linarith, refl }

@[simp] lemma cast_succ_zero {n : ℕ} : fin.cast_succ (0 : fin (n + 1)) = 0 := rfl

lemma fin_coe_succ_eq_succ (i : fin n) : ((i : fin (n + 1)) + 1) = i.succ :=
begin
  simp [fin.one_val, fin.eq_iff_veq],
  norm_cast,
  apply fin.coe_coe_of_lt,
  exact add_lt_add_right i.is_lt 1
end

end succ

section dot_product

variables (i j : fin n)
variables (A : matrix (fin n) (fin n) R)

@[simp] lemma one_dot_product_row :
  dot_product ((1 : matrix (fin n) (fin n) R) i) (λ ix, A ix j) = A i j :=
by simp [dot_product, matrix.one_val]

@[simp] lemma dot_product_one_column :
  dot_product (A i) (λ ix, (1 : matrix (fin n) (fin n) R) ix j) = A i j :=
by simp [dot_product, matrix.one_val]

@[simp] lemma dot_product_std_left (c : R) (k l : fin n) :
  dot_product (std_basis_matrix i j c k) (λ ix, A ix l) = ite (k = i) (c * A j l) 0 :=
begin
  simp [dot_product, std_basis_matrix],
  by_cases hi : (k = i);
  simp [hi]
end

@[simp] lemma dot_product_std_right (c : R) (k l : fin n) :
  dot_product (A k) (λ ix, std_basis_matrix i j c ix l) = ite (l = j) (c * A k i) 0 :=
begin
  simp [dot_product, std_basis_matrix],
  by_cases hj : (l = j);
  simp [hj, mul_comm]
end

end dot_product

section swap

variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)

def swap_row (i j) (h : i ≠ j) : matrix (fin (n + 2)) (fin (m + 2)) R :=
update_row (update_row A i (A j)) j (A i)

def swap_column (i j) (h : i ≠ j) : matrix (fin (n + 2)) (fin (m + 2)) R :=
update_column (update_column A i (λ k, A k j)) j (λ k, A k i)

@[simp] lemma swap_row_def (i j) (h : i ≠ j) :
  swap_row A i j h = update_row (update_row A i (A j)) j (A i) := rfl

@[simp] lemma swap_column_def (i j) (h : i ≠ j) :
  swap_column A i j h = update_column (update_column A i (λ k, A k j)) j (λ k, A k i) := rfl

lemma swap_row_symmetric (i j) (h : i ≠ j) :
  swap_row A i j h = swap_row A j i h.symm :=
begin
  ext ix jx,
  by_cases hj : (ix = j);
  by_cases hi : (ix = i),
  { rw [<-hi, <-hj] at h, contradiction },
  { simp [update_row_ne hi], simp [hj] },
  { simp [update_row_ne hj], simp [hi] },
  { simp [update_row_ne hj, update_row_ne hi] }
end

lemma swap_column_symmetric (i j) (h : i ≠ j) :
  swap_column A i j h = swap_column A j i h.symm :=
begin
  ext ix jx,
  by_cases hj : (jx = j);
  by_cases hi : (jx = i),
  { rw [<-hi, <-hj] at h, contradiction },
  { simp [update_column_ne hi], simp [hj] },
  { simp [update_column_ne hj], simp [hi] },
  { simp [update_column_ne hj, update_column_ne hi] }
end

@[simp] lemma swap_row_swap_row (i j) (h : i ≠ j) :
  swap_row (swap_row A i j h) i j h = A :=
begin
  ext ix jx,
  by_cases hj : (ix = j);
  by_cases hi : (ix = i);
  simp [hi, hj, h],
end

@[simp] lemma swap_column_swap_column (i j) (h : i ≠ j) :
  swap_column (swap_column A i j h) i j h = A :=
begin
  ext ix jx,
  by_cases hj : (jx = j);
  by_cases hi : (jx = i);
  simp [hi, hj, h],
end

end swap

section swap_matrix

variables (i j : fin (n + 2)) (h : i ≠ j)
variables (A : matrix (fin (n + 2)) (fin (n + 2)) R)
include h

def swap_row_matrix : matrix (fin (n + 2)) (fin (n + 2)) R :=
swap_row 1 i j h

def swap_column_matrix : matrix (fin (n + 2)) (fin (n + 2)) R :=
swap_column 1 i j h

@[simp] lemma swap_row_matrix_def :
  (swap_row_matrix i j h : matrix (fin (n + 2)) (fin (n + 2)) R) = swap_row 1 i j h := rfl

@[simp] lemma swap_column_matrix_def :
  (swap_column_matrix i j h : matrix (fin (n + 2)) (fin (n + 2)) R) = swap_column 1 i j h := rfl

@[simp] lemma swap_row_mul_eq_swap_row : swap_row_matrix i j h * A = swap_row A i j h :=
begin
  ext ix jx,
  by_cases hj : (ix = j);
  by_cases hi : (ix = i);
  simp [hi, hj, h, matrix.mul],
end

@[simp] lemma swap_column_mul_eq_swap_column : A * swap_column_matrix i j h = swap_column A i j h :=
begin
  ext ix jx,
  by_cases hj : (jx = j);
  by_cases hi : (jx = i);
  simp [hi, hj, h, matrix.mul],
end

end swap_matrix

section scale

variables (A : matrix (fin n) (fin m) R)

def scale_row (i) (c : R) : matrix (fin n) (fin m) R := update_row A i (λ j, c * A i j)

def scale_column (j) (c : R) : matrix (fin n) (fin m) R := update_column A j (λ i, c * A i j)

@[simp] lemma scale_row_def (i) (c : R) :
  scale_row A i c = update_row A i (λ j, c * A i j) := rfl

@[simp] lemma scale_column_def (j) (c : R) :
  scale_column A j c = update_column A j (λ i, c * A i j) := rfl

end scale

section scale_matrix

variables (A : matrix (fin n) (fin n) R)

def scale_matrix (i) (c : R) : matrix (fin n) (fin n) R := diagonal (λ k, ite (i = k) c 1)

@[simp] lemma scale_matrix_def {n : ℕ} (i) (c : R) :
  @scale_matrix R _ n i c = diagonal (λ k, ite (i = k) c 1) := rfl

@[simp] lemma scale_matrix_row (i) (c : R) : scale_matrix i c * A = scale_row A i c :=
begin
  ext ix jx,
  by_cases hi : (i = ix),
  { simp [hi] },
  { simp [hi, update_row_ne (ne.symm hi)] }
end

@[simp] lemma scale_matrix_column (j) (c : R) : A * scale_matrix j c = scale_column A j c :=
begin
  ext ix jx,
  by_cases hj : (j = jx),
  { simp [hj, mul_comm] },
  { simp [hj, update_column_ne (ne.symm hj), mul_comm] }
end

end scale_matrix

section add_row_col

variables (A : matrix (fin n) (fin m) R)

def add_row (i j) : matrix (fin n) (fin m) R :=
update_row A i (λ k, A i k + A j k)

def add_column (i j) : matrix (fin n) (fin m) R :=
update_column A i (λ k, A k i + A k j)

@[simp] lemma add_row_def (i j) :
  add_row A i j = update_row A i (λ k, A i k + A j k) := rfl

@[simp] lemma add_column_def (i j) :
  add_column A i j = update_column A i (λ k, A k i + A k j) := rfl

end add_row_col

section add_row_col_matrix

variables (i j : fin (n + 2))
variables (A : matrix (fin (n + 2)) (fin (n + 2)) R)

def add_row_matrix : matrix (fin (n + 2)) (fin (n + 2)) R :=
matrix.std_basis_matrix i j 1 + 1

def add_column_matrix : matrix (fin (n + 2)) (fin (n + 2)) R :=
matrix.std_basis_matrix j i 1 + 1

@[simp] lemma add_row_matrix_def : @add_row_matrix R _ n i j = matrix.std_basis_matrix i j 1 + 1 := rfl

@[simp] lemma add_column_matrix_def : @add_column_matrix R _ n i j = matrix.std_basis_matrix j i 1 + 1 := rfl

@[simp] lemma add_row_matrix_eq : add_row_matrix i j * A = add_row A i j :=
begin
  ext ix jx,
  by_cases hi : (i = ix);
  by_cases h : (j = i);
  simp [h, hi, matrix.mul, matrix.add_mul, add_comm];
  simp [ne.symm hi, matrix.mul, matrix.add_mul, add_comm]
end

@[simp] lemma add_column_matrix_eq : A * add_column_matrix i j = add_column A i j :=
begin
  ext ix jx,
  by_cases hi : (i = jx);
  by_cases h : (j = i);
  simp [h, hi, matrix.mul, matrix.mul_add, add_comm];
  simp [ne.symm hi, matrix.mul, matrix.mul_add, add_comm],
end

end add_row_col_matrix

section det

variables (A B : matrix (fin (n + 2)) (fin (n + 2)) R)

def det' {R : Type*} [field R] :
    Π {n : ℕ}, matrix (fin n) (fin n) R -> fin n -> R
| 0 _ _ := 1
| 1 M i := M i i
| (n + 2) M ⟨0, h⟩ := ∑ j, (M 0 j * (-1 : R) ^ (j.val) * det' (minor M (fin.succ_above ⟨0, h⟩) (fin.succ_above j)) 0)
| (n + 2) M ⟨k + 1, hk⟩ := ∑ j, (M ⟨k + 1, hk⟩ j * (-1 : R) ^ (k + 1 + j.val) * det' (minor M (fin.succ_above ⟨k + 1, hk⟩) (fin.succ_above j))
      ⟨k, (add_lt_add_iff_right 1).mp hk⟩)

@[simp] lemma det_zero_eq_one (A : matrix (fin 0) (fin 0) R) {i} : det' A i = 1 := rfl

@[simp] lemma det_one_eq_elem (A : matrix (fin 1) (fin 1) R) {i} : det' A i = A i i := rfl

@[simp] lemma det_laplace_zero {h : 0 < n + 2} :
  det' A 0 = ∑ j, (A 0 j * (-1 : R) ^ (j.val) * det' (minor A (fin.succ_above ⟨0, h⟩) (fin.succ_above j)) 0) := rfl

@[simp] lemma det_laplace_nonzero {i} (h : i + 1 < n + 2) :
  det' A ⟨i + 1, h⟩ = ∑ j, (A ⟨i + 1, h⟩ j * (-1 : R) ^ (i + 1 + j.val) * det' (minor A (fin.succ_above ⟨i + 1, h⟩) (fin.succ_above j))
      ⟨i, (add_lt_add_iff_right 1).mp h⟩) := rfl

@[simp] lemma det_laplace_nonzero' {i : fin (n + 1)} :
  det' A i.succ = ∑ j, (A i.succ j * (-1 : R) ^ (i.val + 1 + j.val) * det' (minor A (fin.succ_above i.succ) (fin.succ_above j)) i) :=
begin
  cases i with i h,
  rw <-add_lt_add_iff_right 1 at h,
  exact det_laplace_nonzero A h,
end

@[simp] lemma det_laplace_nonzero'' (i : fin (n + 1)) :
  det' A (i + 1) = ∑ j, (A (i + 1) j * (-1 : R) ^ (i.val + 1 + j.val) * det' (minor A (fin.succ_above (i + 1)) (fin.succ_above j)) i) :=
by { rw fin_coe_succ_eq_succ, exact det_laplace_nonzero' A }

lemma det_swap_col_eq_neg_det {i j} (h : i ≠ j) :
  det' A 0 = - det' (swap_column A i j h) 0 :=
begin
  simp,
  obtain ⟨i, hi⟩ := i,
  obtain ⟨j, hj⟩ := j,
  induction j with j IHj,
  have key : ∀ f : fin (n + 2) → R, - ∑ k, f k = ∑ k, - f k,
    { intro f, exact (finset.univ.sum_hom has_neg.neg).symm },
  rw key,
  congr,
  ext jx,
  simp [hi, hj],
  sorry
end

lemma det_mul_eq_mul_det :
  det' (A * B) 0 = det' A 0 * det' B 0 :=
begin
  sorry
end


lemma det_eq_det (A : matrix (fin n) (fin n) R) {i j} (h : i ≠ j) : det' A i = det' A j :=
begin
  induction n with n hn,
  { exact fin.elim0 i },
  cases n,
  { rw subsingleton.elim i j },
  refine fin.cases _ _ i,
  refine fin.cases _ _ j,
  { simp },
  { intros ii,
    simp,
    congr,
    ext jj,
    refine fin.cases _ _ ii,
    simp [hn],
    -- have h' := hn (A.minor (fin.succ_above 0) jj.succ_above),
    change A 0 jj * (-1) ^ jj.val * det' (A.minor (0 : fin (n + 2)).succ_above jj.succ_above) 0 =
    A 1 jj * (-1) ^ (1 + jj.val) * det' (A.minor (1 : fin (n + 2)).succ_above jj.succ_above) 0,
    have l00 : (0 : fin 2).succ_above (0 : fin 1) = 1 := rfl,
    have l00' : (0 : fin 3).succ_above (0 : fin 2) = 1 := rfl,
    have l10 : (1 : fin 2).succ_above (0 : fin 1) = 0 := rfl,
    simp only [forall_prop_of_false, det_one_eq_elem, not_true, ne.def, not_false_iff, eq_iff_true_of_subsingleton, minor, l00, l10],
    -- rw (show (1 : fin 2) = (0 : fin 1).succ, by { refl }),
    sorry,
    },

end

end det
