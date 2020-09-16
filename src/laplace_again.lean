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
| (n + 2) M := ∑ j, (M 0 j * (-1 : R) ^ (j : ℕ) * det' (drop M 0 j))


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
  { exact absurd fin.one_pos (not_lt_of_le hl) },
  { rw [←this h.symm, swap_row_symmetric] }
end

lemma fin.succ_above_succ_above_swap (x y : fin (n + 2)) (h : y ≠ x) (j : fin n) :
  x.succ_above ((x.pred_above y h).succ_above j) =
  y.succ_above ((y.pred_above x (ne.symm h)).succ_above j) :=
begin
  wlog H : y < x using [x y],
  { rcases lt_trichotomy x y with H|rfl|H,
    { exact or.inr H },
    { contradiction },
    { exact or.inl H } },
  unfold fin.pred_above,
  rw [dif_pos H, dif_neg (not_lt_of_lt H)],
  have H' := fin.lt_iff_coe_lt_coe.mp H,
  have posx : 0 < x.val := lt_of_le_of_lt (fin.zero_le y) ‹y < x›,
  unfold fin.succ_above,
  all_goals { simp_rw [fin.lt_iff_coe_lt_coe] at * },
  split_ifs,
  any_goals { refl <|> rw fin.cast_succ_fin_succ },
  all_goals {
    simp only [fin.val_eq_coe, fin.coe_cast_lt,
               fin.coe_succ, fin.coe_cast_succ, fin.coe_pred,
               not_lt, ne.def, fin.cast_succ_inj] at * },
  { have hj : (x : ℕ) - 1 = j :=
      le_antisymm ‹(x : ℕ) - 1 ≤ j› (nat.le_pred_of_lt ‹(j : ℕ) < x›),
    rw ←hj at *,
    rw nat.sub_add_one posx at *,
    exact absurd ‹(y : ℕ) < x› (not_lt_of_lt ‹(x : ℕ) < y›) },
  { have hj : (x : ℕ) - 1 = j :=
      le_antisymm ‹(x : ℕ) - 1 ≤ j› (nat.le_pred_of_lt ‹(j : ℕ) < x›),
    rw ←hj at *,
    rw nat.sub_add_one posx at *,
    have hy : y = x :=
      le_antisymm ‹(y : ℕ) ≤ x› (nat.le_of_pred_lt ‹(x : ℕ) - 1 < y›),
    exact absurd hy h },
  { exact absurd ‹(x : ℕ) ≤ j› (nat.not_lt_pred_ge ‹(j : ℕ) < x - 1›) },
  { have hy : (y : ℕ) = j + 1 :=
      le_antisymm ‹(y : ℕ) ≤ j + 1› ‹(j : ℕ) < y›,
    have : (j : ℕ) < x,
      { refine lt_trans (nat.lt_succ_self j) _,
        convert fin.lt_iff_coe_lt_coe.mp H,
        rw hy },
    exact absurd ‹(j : ℕ) < x› (not_lt_of_ge ‹(x : ℕ) ≤ j›) },
  { have : (x : ℕ) ≤ j + 1 :=
      nat.le_add_of_sub_le_right ‹(x : ℕ) - 1 ≤ j›,
    exact absurd ‹(j : ℕ) + 1 < x› (not_lt_of_ge ‹(x : ℕ) ≤ j + 1›) },
  { have : (j : ℕ) + 1 < x :=
      nat.add_lt_of_lt_sub_right ‹(j : ℕ) < x - 1›,
    exact absurd ‹(j : ℕ) + 1 < x› (not_lt_of_ge ‹(x : ℕ) ≤ j + 1›) },
  { have : (j : ℕ) < y :=
      lt_trans (nat.lt_succ_self j) ‹(j : ℕ) + 1 < y›,
    exact absurd ‹(j : ℕ) < y› (not_lt_of_ge ‹(y : ℕ) ≤ j›) },
end

lemma det_swap_01_sum_aux (A : matrix (fin (n + 2)) (fin (n + 2)) R) :
  (∑ x, (∑ y, -A 0 x * (-1) ^ (x : ℕ) * A 1 (x.succ_above y) * (-1) ^ (y : ℕ) *
    det' (λ (i j : fin n), A i.succ.succ (x.succ_above (y.succ_above j))))) =
  ∑ x, (∑ y, A 1 x * (-1) ^ (x : ℕ) * A 0 (x.succ_above y) * (-1) ^ (y : ℕ) *
    det' (λ (i j : fin n), A i.succ.succ (x.succ_above (y.succ_above j)))) :=
begin
  have lhs :
    (∑ x : fin (n + 2), ∑ y : fin (n + 1),
      (A 0 x * (A 1 (x.succ_above y) * (det' (λ (i j : fin n),
        A i.succ.succ (x.succ_above (y.succ_above j))) *
          ((-1) ^ (x : ℕ) * -(-1) ^ (y : ℕ))))))
    = ∑ x : fin (n + 2), ∑ y : fin (n + 2), dite (x = y) (λ _, 0)
      (λ h, (A 0 x * (A 1 y * det' (λ (i j : fin n),
        A i.succ.succ (x.succ_above ((x.pred_above y (ne.symm h)).succ_above j))) *
          -((-1 : R) ^ (x : ℕ) * (-1) ^ (y : ℕ) * ite (y < x) 1 (-1))))),
    { congr' 1 with x,
      rw [fin.sum_univ_succ_above _ x, dif_pos rfl, zero_add],
      congr' 1 with y,
      simp_rw [dif_neg (fin.succ_above_ne x y).symm,
               fin.succ_above_lt_iff, fin.pred_above_succ_above],
      split_ifs with H H,
      { rw [fin.succ_above_below _ _ H],
        ring_exp },
      { rw [fin.succ_above_above _ _ (le_of_not_lt H), fin.coe_succ],
        ring_exp } },
  have rhs :
    (∑ x : fin (n + 2), ∑ y : fin (n + 1),
      (A 1 x * (A 0 (x.succ_above y) * (det' (λ (i j : fin n),
        A i.succ.succ (x.succ_above (y.succ_above j))) *
          ((-1 : R) ^ (x : ℕ) * (-1) ^ (y : ℕ))))))
    = ∑ x : fin (n + 2), ∑ y : fin (n + 2), dite (x = y) (λ _, 0)
      (λ h, (A 1 x * (A 0 y * det' (λ (i j : fin n),
        A i.succ.succ (x.succ_above ((x.pred_above y (ne.symm h)).succ_above j)))
        * ((-1 : R) ^ (x : ℕ) * (-1) ^ (y : ℕ) * ite (y < x) 1 (-1))))),
    { congr' 1 with x,
      rw [fin.sum_univ_succ_above _ x, dif_pos rfl, zero_add],
      congr' 1 with y,
      simp_rw [dif_neg (fin.succ_above_ne x y).symm,
               fin.succ_above_lt_iff, fin.pred_above_succ_above],
      split_ifs with H H,
      { rw [fin.succ_above_below _ _ H],
        ring_exp },
      { rw [fin.succ_above_above _ _ (le_of_not_lt H), fin.coe_succ],
        ring_exp } },
  ring_exp,
  rw [lhs, rhs, finset.sum_comm],
  clear lhs rhs,
  congr' 1 with x,
  congr' 1 with y,
  rcases lt_trichotomy x y with h|h|h,
  { rw [dif_neg (ne_of_lt h)],
    rw [dif_neg (ne_of_gt h), if_neg (not_lt_of_lt h), if_pos h],
    simp [fin.pred_above_succ_above, fin.succ_above_succ_above_swap x y (ne_of_gt h)],
    ring_exp },
  { rw [dif_pos h, dif_pos h.symm] },
  { rw [dif_neg (ne_of_lt h)],
    rw [dif_neg (ne_of_gt h), if_neg (not_lt_of_lt h), if_pos h],
    simp [fin.pred_above_succ_above, fin.succ_above_succ_above_swap y x (ne_of_gt h)],
    ring_exp }
end

lemma det_swap_eq_neg_det (A : matrix (fin (n + 2)) (fin (n + 2)) R) :
  det' (swap_row A 0 1) = - det' A :=
begin
  induction n with n hn,
  { exact det_swap_eq_neg_det_dim2 A 1 0 (fin.zero_ne_one.symm) },
  have s1 : ∀ ix : fin (n + 1), A.swap_row 0 1 ix.succ.succ = A ix.succ.succ,
    { intro ix,
      ext col,
      rw swap_row_ne_apply,
      { exact ne_of_gt (fin.succ_pos _) },
      { exact fin.succ_succ_ne_one _ } },
  symmetry,
  convert det_swap_01_sum_aux A;
  { simp [det_laplace_def, minor, s1, finset.mul_sum],
    ring_exp }
end

end det
