import data.matrix.basic

open_locale matrix

variables {n m : ℕ}

open matrix

namespace matrix

section dot_product

variables {R : Type*} [semiring R]
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

variables {R : Type*} [semiring R]
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

variables {R : Type*} [semiring R]
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

variables {R : Type*} [semiring R]
variables (A : matrix (fin n) (fin m) R)

def scale_row (i) (c : R) : matrix (fin n) (fin m) R := update_row A i (λ j, c * A i j)

def scale_column (j) (c : R) : matrix (fin n) (fin m) R := update_column A j (λ i, c * A i j)

@[simp] lemma scale_row_def (i) (c : R) :
  scale_row A i c = update_row A i (λ j, c * A i j) := rfl

@[simp] lemma scale_column_def (j) (c : R) :
  scale_column A j c = update_column A j (λ i, c * A i j) := rfl

end scale

section scale_matrix

variables {R : Type*}
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

variables {R : Type*} [semiring R]
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

variables {R : Type*} [semiring R]
variables {n' m' : ℕ}

def submatrix (A : matrix (fin n) (fin m) R) (hn : n' ≤ n) (hm : m' ≤ m) : matrix (fin n') (fin m') R :=
λ i j, A (fin.cast_le hn i) (fin.cast_le hm j)

end submatrix

section add_row_col_matrix

variables {R : Type*} [semiring R]
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

variables {R : Type*} [semiring R]

def row_echelon (A : matrix (fin n) (fin m) R) := ∀ i : fin n, ∀ j : fin m, j.val < i.val → A i j = 0

structure rr_echelon (A : matrix (fin n) (fin m) R) : Prop :=
(echelon : row_echelon A)
(leading : ∀ i : fin n, (∀ j : fin m, (∀ lj : fin m, lj < j → A i lj = 0) → A i j ≠ 0 → A i j = 1))

end echelon

section drop

variables {R : Type*} [semiring R]
variables (A : matrix (fin (n + 2)) (fin (m + 2)) R)

def drop (i : fin (n + 2)) (j : fin (m + 2)) : matrix (fin (n + 1)) (fin (m + 1)) R := minor A (i.succ_above) (j.succ_above)

@[simp] lemma drop_def (i j) : drop A i j = minor A (i.succ_above) (j.succ_above) := rfl

@[simp] lemma drop_zero_column (i) : drop A i 0 = minor A (i.succ_above) (fin.succ) :=
by { ext, simp [minor] }

@[simp] lemma drop_zero_row (j) : drop A 0 j = minor A (fin.succ) (j.succ_above) :=
by { ext, simp [minor] }

@[simp] lemma drop_zero_row_column : drop A 0 0 = minor A fin.succ fin.succ :=
by { ext, simp [minor] }

@[simp] lemma drop_last_column (i) : drop A i (fin.last _) = minor A (i.succ_above) (fin.cast_succ) :=
by { ext, simp [minor] }

@[simp] lemma drop_last_row (j) : drop A (fin.last _) j = minor A (fin.cast_succ) (j.succ_above) :=
by { ext, simp [minor] }

@[simp] lemma drop_last_row_column : drop A (fin.last _) (fin.last _) = minor A fin.cast_succ fin.cast_succ :=
by { ext, simp [minor] }

end drop

end matrix
