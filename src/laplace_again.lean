import data.matrix.notation
import data.nat.basic
import data.equiv.basic
import group_theory.perm.sign
import tactic.ring
import tactic.linarith
import tactic.ring_exp
import tactic.apply_fun
import tactic.wlog
import .extra_fin
import .extra_matrix
import linear_algebra.determinant

open_locale big_operators matrix

variables {R : Type*} [field R]
variables {n m : ℕ}

open matrix

section det

variables (A B : matrix (fin (n + 2)) (fin (n + 2)) R)

def det' {R : Type*} [field R] :
    Π {n : ℕ}, matrix (fin n) (fin n) R -> R
| 0 _ := 1
| 1 M := M 0 0
| (n + 2) M := ∑ j, (M 0 j * (-1 : R) ^ (j.val) * det' (drop M 0 j))


@[simp] lemma det_zero_eq_one (A : matrix (fin 0) (fin 0) R) : det' A = 1 := rfl

@[simp] lemma det_one_eq_elem (A : matrix (fin 1) (fin 1) R) : det' A = A 0 0 := rfl

lemma det_laplace_def : det' A = ∑ j, (A 0 j * (-1 : R) ^ (j.val) * det' (drop A 0 j)) := rfl

instance fin_inhabited {n : ℕ} : inhabited (fin (n + 1)) := ⟨0⟩

@[simp] lemma fin.default_eq_zero {n : ℕ} : default (fin (n + 1)) = 0 := rfl

@[simp] lemma fin.default_succ_eq_one {n : ℕ} : fin.succ (default (fin (n + 1))) = 1 := rfl

lemma det_swap_eq_neg_det_dim2 (A : matrix (fin 2) (fin 2) R) (i j) (h : i ≠ j) : det' (swap_row A j i) = - det' A :=
begin
  wlog hl : i ≤ j,
  fin_cases i;
  fin_cases j,
  any_goals { contradiction },
  { simp [det_laplace_def, minor, fin.sum_univ_succ, h.symm, fin.succ_above_below, fin.one_pos],
    ring },
  { exact absurd nat.one_pos (not_lt_of_le (fin.le_iff_val_le_val.mp hl)) },
  { rw [←this h.symm, swap_row_symmetric] }
end

lemma pow_succ_above {n : ℕ} (x : fin (n + 1)) (y : fin n) : (-1 : R) ^ ((x.succ_above y).val) = ite (y.cast_succ < x) ((-1) ^ (y.val)) ((-1) ^ (y.val + 1)) :=
begin
  unfold fin.succ_above,
  split_ifs;
  simp
end

lemma fin.sum_of_succ_above {n : ℕ} (p : fin (n + 1)) (f : fin (n + 1) → R) :
  f p + (∑ x : fin n, f (p.succ_above x)) = ∑ y : fin (n + 1), f y :=
begin
  rw ←finset.sum_insert,
end

lemma det_swap_eq_neg_det_dim3 (A : matrix (fin (n + 2)) (fin (n + 2)) R) : det' (swap_row A 0 1) = - det' A :=
begin
  induction n with n hn,
  { exact det_swap_eq_neg_det_dim2 A 1 0 (fin.zero_ne_one.symm) },
  have s1 : ∀ ix : fin (n + 1), A.swap_row 0 1 ix.succ.succ = A ix.succ.succ,
    { intro ix,
      ext col,
      rw swap_row_ne_apply,
      { exact ne_of_gt (fin.succ_pos _) },
      { exact fin.succ_succ_ne_one } },
  have sumswap :
    ∑ x, (∑ y, -A 0 x * (-1) ^ (x.val) * A 1 (x.succ_above y) * (-1) ^ (y.val)) =
    ∑ x, (∑ y, A 1 x * (-1) ^ x.val * A 0 (x.succ_above y) * (-1) ^ (y.val)),
    { simp [fin.succ_above, ←finset.sum_neg_distrib],
      -- congr' 1,
      -- ext x,
      -- congr' 1,
      -- ext y,
      have : ∀ row, ∀ x, ∀ y : fin (n + 2), A row (ite (y.cast_succ < x) y.cast_succ y.succ) = ite (y.cast_succ < x) (A row y.cast_succ) (A row y.succ),
        { intros row x y, exact apply_ite (A row) (fin.cast_succ y < x) (fin.cast_succ y) (fin.succ y) },
      simp only [neg_mul_eq_neg_mul],
      simp only [this, ite_mul, mul_ite],
      /-
R : Type u_1,
_inst_1 : field R,
n : ℕ,
hn : ∀ (A : matrix (fin (n + 2)) (fin (n + 2)) R), det' (A.swap_row 0 1) = -det' A,
A : matrix (fin (n.succ + 2)) (fin (n.succ + 2)) R,
s1 : ∀ (ix : fin (n + 1)), A.swap_row 0 1 ix.succ.succ = A ix.succ.succ,
this :
  ∀ (row : fin (n.succ + 2)) (x : fin (n + 2 + 1)) (y : fin (n + 2)),
    A row (ite (y.cast_succ < x) y.cast_succ y.succ) = ite (y.cast_succ < x) (A row y.cast_succ) (A row y.succ)
⊢ ∑ (x : fin (n.succ + 2)),
      (∑ (x_1 : fin (n.succ + 1)) in
           finset.filter (λ (x_1 : fin (n.succ + 1)), x_1.cast_succ < x) finset.univ,
           -A 0 x * (-1) ^ x.val * A 1 x_1.cast_succ * (-1) ^ x_1.val +
         ∑ (x_1 : fin (n.succ + 1)) in
           finset.filter (λ (x_1 : fin (n.succ + 1)), ¬x_1.cast_succ < x) finset.univ,
           -A 0 x * (-1) ^ x.val * A 1 x_1.succ * (-1) ^ x_1.val) =
    ∑ (x : fin (n.succ + 2)),
      (∑ (x_1 : fin (n.succ + 1)) in
           finset.filter (λ (x_1 : fin (n.succ + 1)), x_1.cast_succ < x) finset.univ,
           A 1 x * (-1) ^ x.val * A 0 x_1.cast_succ * (-1) ^ x_1.val +
         ∑ (x_1 : fin (n.succ + 1)) in
           finset.filter (λ (x_1 : fin (n.succ + 1)), ¬x_1.cast_succ < x) finset.univ,
           A 1 x * (-1) ^ x.val * A 0 x_1.succ * (-1) ^ x_1.val)
-/

      simp_rw [finset.sum_ite],
      have rs : ∀ f : fin (n + 1) → R, ∀ x : fin (n + 1), ∑ (y : fin n) in finset.filter (λ z : fin n, z.cast_succ < x) finset.univ, f y.cast_succ =
        ∑ y : fin (n + 1) in finset.filter (λ z : fin (n + 1), z < x) finset.univ, f y,
      { sorry },
      simp [rs],
    },
  rw det_laplace_def,
  simp_rw [@det_laplace_def _ _ n],
  simp [minor, fin.succ_above_below, fin.one_pos, s1, mul_add, add_assoc],
  simp_rw [finset.mul_sum],
  symmetry,
  rw [det_laplace_def, ←finset.sum_neg_distrib],
  simp_rw [neg_mul_eq_neg_mul, @det_laplace_def _ _ n],
  simp [minor, fin.succ_above_below, fin.one_pos, s1, mul_add, add_assoc, ←finset.sum_neg_distrib],
  simp_rw [finset.mul_sum, ←finset.sum_neg_distrib, neg_mul_eq_neg_mul],
  simp [sumswap],
end

end det
