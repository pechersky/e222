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

lemma det_swap_eq_neg_det_dim3 (A : matrix (fin (n + 2)) (fin (n + 2)) R) : det' (swap_row A 0 1) = - det' A :=
begin
  induction n with n hn,,
  { exact det_swap_eq_neg_det_dim2 A 1 0 (fin.zero_ne_one.symm) }
  rw det_laplace_def,
  rw fin.sum_univ_succ,
    simp [minor, fin.succ_above_below, fin.one_pos, s1, mul_add, add_assoc],
end

end det
