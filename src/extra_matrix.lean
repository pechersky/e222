import data.matrix.basic
import tactic.fin_cases
import .extra_fin

open_locale matrix

variables {n m : ℕ}
variables {R : Type*}

open matrix

namespace matrix

section dot_product

variables [semiring R]
variables (A : matrix (fin n) (fin m) R)

@[simp] lemma one_dot_product_row (i j) :
  dot_product ((1 : matrix (fin n) (fin n) R) i) (λ ix, A ix j) = A i j :=
by simp [dot_product, matrix.one_apply]

@[simp] lemma dot_product_one_column (i j) :
  dot_product (A i) (λ ix, (1 : matrix (fin m) (fin m) R) ix j) = A i j :=
by simp [dot_product, matrix.one_apply]

@[simp] lemma dot_product_std_left (c : R) (i : fin m) (j : fin n) (k l : fin m) :
  dot_product (std_basis_matrix i j c k) (λ ix, A ix l) = ite (k = i) (c * A j l) 0 :=
begin
  simp [dot_product, std_basis_matrix],
  by_cases hi : (k = i);
  simp [hi]
end

@[simp] lemma dot_product_std_right (c : R) (i : fin m) (j k l : fin n) :
  dot_product (A k) (λ ix, std_basis_matrix i j c ix l) = ite (l = j) (A k i * c) 0 :=
begin
  simp [dot_product, std_basis_matrix],
  by_cases hj : (l = j);
  simp [hj],
end

end dot_product

section swap

variables [semiring R]
variables (A : matrix (fin n) (fin m) R)

def swap_row (i j) : matrix (fin n) (fin m) R :=
A ∘ equiv.swap i j

def swap_column (i j) : matrix (fin n) (fin m) R :=
λ ix jx, A ix (equiv.swap i j jx)

lemma swap_row_def (i j) :
  swap_row A i j = A ∘ equiv.swap i j := rfl

@[simp] lemma swap_row_eq (i) : swap_row A i i = A :=
by { ext ix jx, by_cases hi : (ix = i); simp [swap_row, hi, equiv.swap_apply_of_ne_of_ne] }

lemma swap_column_def (i j) :
  swap_column A i j = λ ix jx, A ix (equiv.swap i j jx) := rfl

@[simp] lemma swap_column_eq (j) : swap_column A j j = A :=
by { ext ix jx, by_cases hj : (jx = j); simp [swap_column, hj, equiv.swap_apply_of_ne_of_ne] }

lemma swap_row_symmetric (i j) :
  swap_row A i j = swap_row A j i :=
begin
  ext ix jx,
  by_cases hj : (ix = j);
  by_cases hi : (ix = i);
  simp [swap_row, hj, hi, equiv.swap_apply_of_ne_of_ne]
end

@[simp] lemma swap_row_apply (i j jx) : swap_row A i j j jx = A i jx :=
by simp [swap_row]

@[simp] lemma swap_row_swap_apply (i j jx) : swap_row A i j i jx = A j jx :=
by { rw swap_row_symmetric, simp [swap_row] }

@[simp] lemma swap_row_ne_apply (i j ix jx) (hi : ix ≠ i) (hj : ix ≠ j) : swap_row A i j ix jx = A ix jx :=
by simp [swap_row, equiv.swap_apply_of_ne_of_ne, hi, hj]

lemma swap_column_symmetric (i j) :
  swap_column A i j = swap_column A j i :=
begin
  ext ix jx,
  by_cases hj : (jx = j);
  by_cases hi : (jx = i);
  simp [swap_column, hj, hi, equiv.swap_apply_of_ne_of_ne]
end

@[simp] lemma swap_column_apply (i j ix) : swap_column A i j ix j = A ix i :=
by simp [swap_column]

@[simp] lemma swap_column_swap_apply (i j ix) : swap_column A i j ix i = A ix j :=
by { rw swap_column_symmetric, simp [swap_column] }

@[simp] lemma swap_column_ne_apply (i j ix jx) (hi : jx ≠ i) (hj : jx ≠ j) : swap_column A i j ix jx = A ix jx :=
by simp [swap_column, equiv.swap_apply_of_ne_of_ne, hi, hj]

@[simp] lemma swap_row_swap_row (i j) :
  swap_row (swap_row A i j) i j = A :=
begin
  ext ix jx,
  by_cases hj : (ix = j);
  by_cases hi : (ix = i);
  simp [swap_row, hi, hj]
end

@[simp] lemma swap_column_swap_column (i j) :
  swap_column (swap_column A i j) i j = A :=
begin
  ext ix jx,
  by_cases hj : (jx = j);
  by_cases hi : (jx = i);
  simp [swap_column, hi, hj],
end

lemma swap_row_thrice (i j k : fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
  swap_row (swap_row (swap_row A i j) j k) i j  = swap_row A i k :=
begin
  ext ix jx,
  by_cases hj : (ix = j),
  rw [hj, swap_row_apply, swap_row_ne_apply _ _ _ _ _ hij hik,
      swap_row_swap_apply, swap_row_ne_apply _ _ _ _ _ hij.symm hjk],
  by_cases hi : (ix = i),
  simp [hi, hik.symm, hjk.symm],
  by_cases hk : (ix = k),
  simp [hk, hik.symm, hjk.symm],
  simp [hi, hj, hk],
end

lemma swap_column_thrice (i j k : fin m) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
  swap_column (swap_column (swap_column A i j) j k) i j  = swap_column A i k :=
begin
  ext ix jx,
  by_cases hj : (jx = j),
  rw [hj, swap_column_apply, swap_column_ne_apply _ _ _ _ _ hij hik,
      swap_column_swap_apply, swap_column_ne_apply _ _ _ _ _ hij.symm hjk],
  by_cases hi : (jx = i),
  simp [hi, hik.symm, hjk.symm],
  by_cases hk : (jx = k),
  simp [hk, hik.symm, hjk.symm],
  simp [hi, hj, hk],
end

end swap

section swap_matrix

variables [semiring R]
variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)

def swap_row_matrix (i j) : matrix (fin (n + 2)) (fin (n + 2)) R :=
swap_row 1 i j

def swap_column_matrix (i j) : matrix (fin (m + 2)) (fin (m + 2)) R :=
swap_column 1 i j

@[simp] lemma swap_row_matrix_def (i j)  :
  (swap_row_matrix i j : matrix (fin (n + 2)) (fin (n + 2)) R) = swap_row 1 i j := rfl

@[simp] lemma swap_column_matrix_def (i j) :
  (swap_column_matrix i j : matrix (fin (n + 2)) (fin (n + 2)) R) = swap_column 1 i j := rfl

@[simp] lemma swap_row_mul_eq_swap_row (i j) : swap_row_matrix i j ⬝ A = swap_row A i j :=
begin
  ext ix jx,
  by_cases hj : (ix = j);
  by_cases hi : (ix = i);
  simp [swap_row, hi, hj, matrix.mul]
end

@[simp] lemma swap_column_mul_eq_swap_column (i j) : A ⬝ swap_column_matrix i j = swap_column A i j :=
begin
  ext ix jx,
  by_cases hj : (jx = j);
  by_cases hi : (jx = i);
  simp [swap_column, hi, hj, matrix.mul]
end

end swap_matrix

section scale

variables [semiring R]
variables (A : matrix (fin n) (fin m) R)

def scale_row (i) (c : R) : matrix (fin n) (fin m) R := update_row A i (λ j, c * A i j)

def scale_column (j) (c : R) : matrix (fin n) (fin m) R := update_column A j (λ i, c * A i j)

@[simp] lemma scale_row_def (i) (c : R) :
  scale_row A i c = update_row A i (λ j, c * A i j) := rfl

@[simp] lemma scale_column_def (j) (c : R) :
  scale_column A j c = update_column A j (λ i, c * A i j) := rfl

end scale

section scale_matrix

variables (A : matrix (fin n) (fin m) R)

def scale_matrix [semiring R] (i) (c : R) : matrix (fin n) (fin n) R := diagonal (λ k, ite (i = k) c 1)

@[simp] lemma scale_matrix_def [semiring R]  {n : ℕ} (i) (c : R) :
  @scale_matrix n R _ i c = diagonal (λ k, ite (i = k) c 1) := rfl

@[simp] lemma scale_matrix_row [semiring R] (i) (c : R) : scale_matrix i c ⬝ A = scale_row A i c :=
begin
  ext ix jx,
  by_cases hi : (i = ix),
  { simp [hi] },
  { simp [hi, update_row_ne (ne.symm hi)] }
end

@[simp] lemma scale_matrix_column [comm_semiring R] (j) (c : R) : A ⬝ scale_matrix j c = scale_column A j c :=
begin
  ext ix jx,
  by_cases hj : (j = jx),
  { simp [hj, mul_comm] },
  { simp [hj, update_column_ne (ne.symm hj), mul_comm] }
end

end scale_matrix

section add_row_col

variables [semiring R]
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

section submatrix

variables [semiring R]
variables {n' m' : ℕ}

def submatrix (A : matrix (fin n) (fin m) R) (hn : n' ≤ n) (hm : m' ≤ m) : matrix (fin n') (fin m') R :=
λ i j, A (fin.cast_le hn i) (fin.cast_le hm j)

end submatrix

section add_row_col_matrix

variables [semiring R]
variables (A : matrix (fin (n + 2)) (fin (n + 2)) R)

def add_row_matrix (i j) : matrix (fin n) (fin m) R :=
dite (m ≤ n)
  (λ h, matrix.std_basis_matrix i j 1 + submatrix (1 : matrix (fin n) (fin n) R) (le_refl _) h)
  (λ h, matrix.std_basis_matrix i j 1 + submatrix (1 : matrix (fin m) (fin m) R) (le_of_not_ge h) (by refl))

def add_column_matrix (i j) : matrix (fin n) (fin m) R :=
dite (m ≤ n)
  (λ h, matrix.std_basis_matrix j i 1 + submatrix (1 : matrix (fin n) (fin n) R) (le_refl _) h)
  (λ h, matrix.std_basis_matrix j i 1 + submatrix (1 : matrix (fin m) (fin m) R) (le_of_not_ge h) (by refl))

@[simp] lemma add_row_matrix_small_def (i j) (h : m ≤ n) :
  (add_row_matrix i j : matrix (fin n) (fin m) R) = matrix.std_basis_matrix i j 1 + submatrix (1 : matrix (fin n) (fin n) R) (le_refl _) h :=
by simp [add_row_matrix, h]

@[simp] lemma add_row_matrix_large_def (i j) (h : n < m) :
  (add_row_matrix i j : matrix (fin n) (fin m) R) = matrix.std_basis_matrix i j 1 + submatrix (1 : matrix (fin m) (fin m) R) (le_of_lt h) (le_refl _) :=
by simp [add_row_matrix, h]

@[simp] lemma add_column_matrix_small_def (i j) (h : m ≤ n) :
  (add_column_matrix j i : matrix (fin n) (fin m) R) = matrix.std_basis_matrix i j 1 + submatrix (1 : matrix (fin n) (fin n) R) (le_refl _) h :=
by simp [add_column_matrix, h]

@[simp] lemma add_column_matrix_large_def (i j) (h : n < m) :
  (add_column_matrix j i : matrix (fin n) (fin m) R) = matrix.std_basis_matrix i j 1 + submatrix (1 : matrix (fin m) (fin m) R) (le_of_lt h) (le_refl _) :=
by simp [add_column_matrix, h]

@[simp] lemma add_row_matrix_eq (i j) : add_row_matrix i j ⬝ A = add_row A i j :=
begin
  ext ix jx,
  by_cases hi : (i = ix);
  by_cases h : (j = i);
  simp [h, hi, matrix.mul, matrix.add_mul, add_comm, submatrix, fin.cast_le, fin.cast_lt];
  simp [ne.symm hi, matrix.mul, matrix.add_mul, add_comm, submatrix, fin.cast_le, fin.cast_lt]
end

@[simp] lemma add_column_matrix_eq (i j) : A ⬝ add_column_matrix i j = add_column A i j :=
begin
  ext ix jx,
  by_cases hi : (i = jx);
  by_cases h : (j = i);
  simp [h, hi, matrix.mul, matrix.mul_add, add_comm, submatrix, fin.cast_le, fin.cast_lt];
  simp [ne.symm hi, matrix.mul, matrix.mul_add, add_comm, submatrix, fin.cast_le, fin.cast_lt],
end

end add_row_col_matrix

section echelon

variables [semiring R]

def row_echelon (A : matrix (fin n) (fin m) R) := ∀ i : fin n, ∀ j : fin m, j.val < i.val → A i j = 0

structure rr_echelon (A : matrix (fin n) (fin m) R) : Prop :=
(echelon : row_echelon A)
(leading : ∀ i : fin n, (∀ j : fin m, (∀ lj : fin m, lj < j → A i lj = 0) → A i j ≠ 0 → A i j = 1))

end echelon

section drop

variables [semiring R]
variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)

def drop (i : fin (n + 2)) (j : fin (m + 2)) : matrix (fin (n + 1)) (fin (m + 1)) R := minor A (i.succ_above) (j.succ_above)

lemma drop_def (i j) : drop A i j = minor A (i.succ_above) (j.succ_above) := rfl

lemma drop_zero_column (i) : drop A i 0 = minor A (i.succ_above) (fin.succ) :=
by { ext, simp [drop_def, minor] }

lemma drop_zero_row (j) : drop A 0 j = minor A (fin.succ) (j.succ_above) :=
by { ext, simp [drop_def, minor] }

lemma drop_zero_row_column : drop A 0 0 = minor A fin.succ fin.succ :=
by { ext, simp [drop_def, minor] }

lemma drop_last_column (i) : drop A i (fin.last _) = minor A (i.succ_above) (fin.cast_succ) :=
by { ext, simp [drop_def, minor] }

lemma drop_last_row (j) : drop A (fin.last _) j = minor A (fin.cast_succ) (j.succ_above) :=
by { ext, simp [drop_def, minor] }

lemma drop_last_row_column : drop A (fin.last _) (fin.last _) = minor A fin.cast_succ fin.cast_succ :=
by { ext, simp [drop_def, minor] }

end drop

section drop_drop

variables [semiring R]
variables (A : matrix (fin (n + 3)) (fin (m + 3)) R)

lemma drop_drop_comm (i i' : fin (n + 3)) (j j') (h : i ≠ i') :
  drop (drop A i' j) (i'.pred_above i h) j' = drop (drop A i j) (i.pred_above i' h.symm) j' :=
by { simp only [drop_def, minor], ext, rw fin.succ_above_succ_above_swap }

lemma drop_drop_comm' (i i') (j j' : fin (m + 3)) (h : j ≠ j') :
  drop (drop A i j') i' (j'.pred_above j h) = drop (drop A i j) i' (j.pred_above j' h.symm) :=
by { simp only [drop_def, minor], ext, rw fin.succ_above_succ_above_swap }

lemma drop_drop_adjacent (i : fin (n + 2)) (j j') :
  drop (drop A i.succ j) i j' = drop (drop A i.cast_succ j) i j' :=
begin
  ext x y,
  simp only [drop_def, minor],
  cases fin.succ_above_lt_ge i x,
  { rw [fin.succ_above_below _ _ h, fin.succ_above_below, fin.succ_above_below _ x.cast_succ],
    { exact h },
    { refine lt_trans _ (fin.cast_succ_lt_succ i),
      exact h } },
  { rw [fin.succ_above_above _ _ h, fin.succ_above_above _ x.succ, fin.succ_above_above _ x.succ],
    { rw [fin.cast_succ_le_cast_succ_iff],
      exact le_trans h (le_of_lt (fin.cast_succ_lt_succ _)) },
    { rw [fin.cast_succ_fin_succ, fin.succ_le_succ_iff],
      exact h } }
end

lemma drop_drop_01 (j j') : drop (drop A 1 j) 0 j' = drop (drop A 0 j) 0 j' :=
drop_drop_adjacent A 0 j j'

lemma drop_drop_0i (i : fin (n + 2)) (j j') :
  drop (drop A i.succ j) 0 j' = drop (drop A 0 j) i j'  :=
begin
  ext x y,
  simp only [drop_def, minor, fin.succ_above_zero],
  cases fin.succ_above_lt_ge i x,
  { rw [fin.succ_above_below _ _ h, fin.succ_above_below _ x.succ, fin.cast_succ_fin_succ],
    { rw [fin.cast_succ_fin_succ, fin.succ_lt_succ_iff],
      exact h } },
  { rw [fin.succ_above_above _ _ h, fin.succ_above_above _ x.succ],
    { rw [fin.cast_succ_fin_succ, fin.succ_le_succ_iff],
      exact h } }
end

end drop_drop

section drop_swap

variables [semiring R]
variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)

@[simp] lemma drop_swap_adjacent (i : fin (n + 1)) (j) :
  drop (swap_row A i.cast_succ i.succ) i.succ j = drop A i.cast_succ j :=
begin
  ext x y,
  simp only [drop_def, minor],
  rcases lt_trichotomy x i with h|rfl|h,
  { rw [fin.succ_above_below _ x, fin.succ_above_below _ x, swap_row_ne_apply],
    { exact ne_of_lt h },
    { exact ne_of_lt (lt_trans (fin.cast_succ_lt_cast_succ_iff.mpr h) (fin.cast_succ_lt_succ _)) },
    { exact h },
    { exact (lt_trans (fin.cast_succ_lt_cast_succ_iff.mpr h) (fin.cast_succ_lt_succ _)) } },
  { rw [fin.succ_above_below _ x (fin.cast_succ_lt_succ _),
        fin.succ_above_above _ x (le_refl _), swap_row_swap_apply] },
  { rw [fin.succ_above_above _ x, fin.succ_above_above _ x, swap_row_ne_apply],
    { exact ne_of_gt (lt_trans (fin.cast_succ_lt_cast_succ_iff.mpr h) (fin.cast_succ_lt_succ _)) },
    { exact ne_of_gt (fin.succ_lt_succ_iff.mpr h) },
    { exact le_of_lt h },
    { rw fin.succ_le_iff_cast_succ_lt,
      exact h } },
end

@[simp] lemma drop_swap_01 (j) : drop (swap_row A 0 1) 1 j = drop A 0 j :=
drop_swap_adjacent A 0 j

@[simp] lemma drop_swap_adjacent' (i : fin (n + 1)) (j) :
  drop (swap_row A i.cast_succ i.succ) i.cast_succ j = drop A i.succ j :=
begin
  ext x y,
  simp only [drop_def, minor],
  rcases lt_trichotomy x i with h|rfl|h,
  { rw [fin.succ_above_below _ x, fin.succ_above_below _ x, swap_row_ne_apply],
    { exact ne_of_lt h },
    { exact ne_of_lt (lt_trans (fin.cast_succ_lt_cast_succ_iff.mpr h) (fin.cast_succ_lt_succ _)) },
    { exact (lt_trans (fin.cast_succ_lt_cast_succ_iff.mpr h) (fin.cast_succ_lt_succ _)) },
    { exact h } },
  { rw [fin.succ_above_below _ x (fin.cast_succ_lt_succ _),
        fin.succ_above_above _ x (le_refl _), swap_row_apply] },
  { rw [fin.succ_above_above _ x, fin.succ_above_above _ x, swap_row_ne_apply],
    { exact ne_of_gt (lt_trans (fin.cast_succ_lt_cast_succ_iff.mpr h) (fin.cast_succ_lt_succ _)) },
    { exact ne_of_gt (fin.succ_lt_succ_iff.mpr h) },
    { rw fin.succ_le_iff_cast_succ_lt,
      exact h },
    { exact le_of_lt h } },
end

@[simp] lemma drop_swap_01' (j) : drop (swap_row A 0 1) 0 j = drop A 1 j :=
drop_swap_adjacent' A 0 j

lemma drop_swap_zero_comm {i j : fin (n + 2)} (h : i ≠ j) (ipos : 0 < i) (jpos : 0 < j) (col) :
    (A.swap_row i j).drop 0 col = (A.drop 0 col).swap_row (i.pred (ne_of_gt ipos)) (j.pred (ne_of_gt jpos)) :=
begin
  ext x y,
  by_cases hxi : x = i.pred (ne_of_gt ipos),
  { simp [hxi, drop_zero_row, minor], },
  by_cases hxj : x = j.pred (ne_of_gt jpos),
  { simp [hxj, drop_zero_row, minor] },
  { rw swap_row_ne_apply _ _ _ _ _ hxi hxj,
    rw fin.pred_succ_iff at hxi hxj,
    simp only [minor, drop_zero_row, swap_row_ne_apply, hxi, hxj, ne.def, not_false_iff] }
end

end drop_swap

section pairwise

variables [semiring R]
variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)
variables (A' : matrix (fin 5) (fin 5) R)

-- def pairwise_swap0_aux : fin (n + 2) → matrix (fin (n + 2)) (fin (m + 2)) R :=
-- λ i, @fin.succ_rec_on (n + 2) i (λ n' i', matrix (fin (n + 2)) (fin (m + 2)) R)
-- (λ _, A)
-- (λ n' i' h, swap_row h i'.cast_succ i'.succ)

-- lemma ps0a : pairwise_swap0_aux A 0 = A := rfl

-- lemma ps0a1 : pairwise_swap0_aux A 1 = A.swap_row 0 1 := rfl

-- lemma ps0a2 : pairwise_swap0_aux A 2 = (A.swap_row 0 1).swap_row 1 2 :=
-- begin
--   unfold pairwise_swap0_aux,
-- end

def pairwise_swap0_aux : ℕ → matrix (fin (n + 2)) (fin (m + 2)) R
| 0 := A
| (nat.succ i) := if h : n + 1 ≤ i
                    then A
                    else let I := (fin.mk i (lt_of_not_ge' h)) in
                    swap_row (pairwise_swap0_aux i) I.cast_succ I.succ

def pairwise_swap0_aux' : ℕ → matrix (fin (n + 2)) (fin (m + 2)) R → matrix (fin (n + 2)) (fin (m + 2)) R
| 0 M := M
| (nat.succ i) M := if h : n + 1 ≤ i
                      then M
                      else let I := (fin.mk i (lt_of_not_ge' h)) in
                      pairwise_swap0_aux' i (swap_row M I.cast_succ I.succ)

def pairwise_swap0' : ℕ → matrix (fin (n + 2)) (fin (m + 2)) R
| 0 := A
| (nat.succ i) := pairwise_swap0_aux' i (pairwise_swap0_aux A i.succ)

def pairwise_swap0 (i : fin (n + 2)) : matrix (fin (n + 2)) (fin (m + 2)) R :=
pairwise_swap0' A i

lemma pairwise_swap0_eq (i : fin (n + 2)) : pairwise_swap0 A i = A.swap_row 0 i :=
begin
  obtain ⟨i, hi⟩ := i,
  ext x y,
  by_cases h : (x = i),
  simp [h, pairwise_swap0, pairwise_swap0'],
  -- cases i with i i,
  -- { simp only [pairwise_swap0, pairwise_swap0', fin.mk_zero, swap_row_eq, fin.coe_zero] },
  -- induction i with i IH,
  -- simp [pairwise_swap0, pairwise_swap0', pairwise_swap0_aux, pairwise_swap0_aux'],
  -- -- have : ((⟨i.succ.succ, hi⟩ : fin (n + 2)) : ℕ) = i.succ.succ := rfl,
  -- -- simp [pairwise_swap0, pairwise_swap0', pairwise_swap0_aux, pairwise_swap0_aux'],
  -- specialize IH (nat.lt_of_succ_lt hi),
  -- simp [pairwise_swap0, pairwise_swap0', pairwise_swap0_aux, pairwise_swap0_aux'] at IH,
  -- rw dif_neg at IH,
  -- simp [pairwise_swap0, pairwise_swap0', pairwise_swap0_aux, pairwise_swap0_aux'],
  -- rw dif_neg,
  -- rw dif_neg,
  -- rw dif_neg,
  -- have : fin.succ (⟨i, _⟩ : fin (n + 1)) = fin.cast_succ (⟨i.succ, _⟩) := rfl,
  -- rw this,
  -- rw swap_row_thrice,
  -- rw ←swap_row_thrice,
  -- rcases eq_or_lt_of_le (fin.zero_le i) with rfl|H,
  -- { simp only [pairwise_swap0, pairwise_swap0', swap_row_eq, fin.coe_zero] },
  -- { set i' := i.pred (ne_of_gt H) with hi,
  --   rw fin.pred_succ_iff at hi,
  --   rw ←hi,
  --   simp only [pairwise_swap0],
  --   rw (show ((i'.succ : ℕ) = (i' : ℕ).succ), by { sorry }),
  --   simp only [pairwise_swap0', pairwise_swap0_aux, pairwise_swap0_aux'],
  --   },
end

end pairwise

section swap_swap

variables [semiring R]
variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)

lemma swap_contract_01 {i : fin (n + 2)} (h : 1 < i) :
  ((A.swap_row 0 1).swap_row 1 i).swap_row 0 1 = A.swap_row 0 i :=
begin
  have hpos : i ≠ 0 := ne_of_gt (lt_of_le_of_lt (fin.zero_le 1) h),
  rw swap_row_thrice A 0 1 i fin.zero_ne_one (ne_of_lt h) hpos.symm
end

end swap_swap

section induction

variables [semiring R]
variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)

@[elab_as_eliminator] protected lemma elem_matrix.induction_on
  {C : Π {n}, matrix (fin n) (fin n) R → fin n → Prop}
  (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i : fin (n + 2))
  (h2 : ∀ (A' : matrix (fin 2) (fin 2) R), ∀ x, C A' x)
  (hn0 : C A 0)
  (hn0e : ∀ n, ∀ (A'' : matrix (fin (n + 2)) (fin (n + 2)) R) (A' : matrix (fin (n + 1)) (fin (n + 1)) R), C A'' 0 → C A' 0)
  (hns : ∀ x : fin (n + 1), ∀ A'', C A'' x → C A x.cast_succ → C A x.succ) :
  C A i :=
begin
  induction n with n hn,
  { exact h2 A i },
  obtain ⟨i, hi⟩ := i,
  induction i with i IH,
  { simp only [fin.mk_zero],
    exact hn0 },
  { set i' : fin (n + 2) := ⟨i, nat.lt_of_succ_lt_succ hi⟩ with hi',
    have hib' : (⟨i.succ, hi⟩ : fin (n + 3)) = i'.succ := rfl,
    rw hib',
    have hin : i < n.succ + 2 := lt_trans (nat.lt_succ_self i) hi,
    specialize IH hin,
    have : (⟨i, hin⟩ : fin (n + 3)) = i'.cast_succ := rfl,
    simp_rw this at IH,
    apply hns i' _ _ IH,
    { apply hn,
      apply hn0e,
      exact hn0,
      { intros j A'' A' pA'' pA',
      },
      },
    {  } },
end


end induction

end matrix
