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

lemma det_swap01_eq_neg_det (A : matrix (fin (n + 2)) (fin (n + 2)) R) :
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

lemma fin.pred_succ_iff (x : fin (n + 1)) (y : fin n) (hx : x ≠ 0) :
  y = x.pred hx ↔ y.succ = x :=
⟨λ h, h.symm ▸ (fin.succ_pred x hx), λ h, by simp_rw [←h, fin.pred_succ] ⟩

lemma det_swap_ij_pos_eq_neg_det (A : matrix (fin (n + 2)) (fin (n + 2)) R)
  (i j : fin (n + 2)) (ipos : 0 < i) (h : i < j) :
  det' (swap_row A i j) = - det' A :=
begin
  induction n with n hn,
  { fin_cases i,
    { exact absurd ipos (lt_irrefl 0) },
    fin_cases j,
    { exact absurd h (not_lt_of_le (fin.zero_le 1)) },
    { exact absurd h (lt_irrefl 1) } },
  set i' := i.pred (ne_of_gt ipos) with hi,
  set j' := j.pred (ne_of_gt (lt_trans ipos h)) with hj,
  have h' : i' < j',
    { simp only [fin.lt_iff_coe_lt_coe, fin.coe_pred],
      exact nat.pred_lt_pred (ne_of_gt ipos) h, },
  have jpos' : 0 < j' := lt_of_le_of_lt (fin.zero_le i') h',
  have drop_swap_comm : ∀ col,
    (A.swap_row i j).drop 0 col = (A.drop 0 col).swap_row i' j',
    { intro col,
      ext x y,
      by_cases hxi : x = i',
      { simp [hxi, minor] },
      by_cases hxj : x = j',
      { simp [hxj, minor] },
      { rw swap_row_ne_apply _ _ _ _ _ hxi hxj,
        rw fin.pred_succ_iff at hxi hxj,
        simp only [minor, drop_zero_row, swap_row_ne_apply,
                    hxi, hxj, ne.def, not_false_iff] } },
  have swap_expand : ∀ {M : matrix (fin (n + 2)) (fin (n + 2)) R} row,
    1 < row → M.swap_row 0 row =
      ((M.swap_row 0 1).swap_row 1 row).swap_row 0 1,
    { intros M row H,
      have hpos : row ≠ 0 := ne_of_gt (lt_of_le_of_lt (fin.zero_le 1) H),
      rw swap_row_thrice M 0 1 row fin.zero_ne_one (ne_of_lt H) hpos.symm },
  rw [det_laplace_def, det_laplace_def],
  simp_rw [←finset.sum_neg_distrib, swap_row_ne_apply _ _ _ _ _
    (ne_of_lt ipos) (ne_of_lt (lt_trans ipos h)), drop_swap_comm],
  cases eq_or_lt_of_le (fin.zero_le i') with H H,
  { rw ←H,
    by_cases Hj : (j' = 1),
    { simp_rw [Hj, det_swap01_eq_neg_det],
      ring_exp, },
    { replace Hj : 1 < j' := lt_of_le_of_ne jpos' (ne.symm Hj),
      simp_rw [swap_expand j' Hj, det_swap01_eq_neg_det,
        hn _ _ _ (lt_of_le_of_ne (fin.zero_le 1) (fin.zero_ne_one)) Hj,
        det_swap01_eq_neg_det],
      ring } },
  { simp_rw hn _ _ _ H h',
    ring }
end

lemma det_swap_0j_eq_neg_det (A : matrix (fin (n + 2)) (fin (n + 2)) R)
  (j : fin (n + 2)) (hj : 1 < j) :
  det' (swap_row A 0 j) = - det' A :=
begin
  have jpos : 0 < j := lt_of_le_of_lt (fin.zero_le 1) hj,
  induction n with n hn,
  { fin_cases j,
    { exact absurd jpos (lt_irrefl 0) },
    { exact det_swap01_eq_neg_det A } },
  have swap_expand : ∀ {M : matrix (fin (n + 3)) (fin (n + 3)) R} row,
    1 < row → M.swap_row 0 row =
      ((M.swap_row 0 1).swap_row 1 row).swap_row 0 1,
    { intros M row H,
      have hpos : row ≠ 0 := ne_of_gt (lt_of_le_of_lt (fin.zero_le 1) H),
      rw swap_row_thrice M 0 1 row fin.zero_ne_one (ne_of_lt H) hpos.symm },
  rw [swap_expand j hj, det_swap01_eq_neg_det,
      det_swap_ij_pos_eq_neg_det _ 1 j
        (lt_of_le_of_ne (fin.zero_le 1) (fin.zero_ne_one)) hj,
      det_swap01_eq_neg_det, neg_neg]
end

lemma det_swap_eq_neg_det (A : matrix (fin (n + 2)) (fin (n + 2)) R)
  (i j) (h : i ≠ j) :
  det' (swap_row A i j) = -det' A :=
begin
  wlog H : i < j using [i j],
  { rcases lt_trichotomy j i with H|rfl|H,
    { exact or.inr H },
    { contradiction },
    { exact or.inl H } },
  { rcases eq_or_lt_of_le (fin.zero_le i) with rfl|hi,
    { by_cases hj : (j = 1),
      { rw hj,
        exact det_swap01_eq_neg_det A },
      { replace hj : 1 < j,
        { refine lt_of_le_of_ne _ (ne.symm hj),
          exact lt_of_le_of_ne (fin.zero_le j) h },
        exact det_swap_0j_eq_neg_det A j hj } },
    { rw det_swap_ij_pos_eq_neg_det A i j hi H } },
  { rw [swap_row_symmetric, this h.symm] }
end

def det'' {R : Type*} [field R] :
    Π {n : ℕ}, matrix (fin n) (fin n) R -> fin n -> R
| 0 _ _ := 1
| 1 M i := M i i
| (n + 2) M i := dite (i = 0)
  (λ h, ∑ j, (M 0 j * (-1 : R) ^ (j : ℕ) * det'' (drop M 0 j) 0))
  (λ h, ∑ j, (M i j * (-1 : R) ^ ((i : ℕ) + j) * det'' (drop M i j) (fin.pred i h)))

lemma det''_eq_det' (A : matrix (fin n) (fin n) R) (i : fin n) :
  det'' A i = det' A :=
begin
  rcases n with _|n,
  { exact fin_zero_elim i },
  induction n with n hn,
  { rw [det'', det', subsingleton.elim i 0] },
  { rcases eq_or_lt_of_le (fin.zero_le i) with rfl|hi,
    { simp only [det'', det', hn, dif_pos] },
    { rw [det'', dif_neg (ne_of_gt hi)],
      rw fin.sum_univ_succ_above _ i,
      rw hn,
      rw ←neg_inj,
      rw neg_add,
      rw neg_mul_eq_mul_neg,
      rw ←finset.sum_neg_distrib,
      symmetry,
      ring_exp,
      rw ←det_swap_eq_neg_det A 0 i (ne_of_lt hi),
      rw det',
      rw fin.sum_univ_succ_above _ i,
      rw mul_assoc,
      ring_exp,
      congr' 2,
      {
        have drop_swap_comm :
          (A.swap_row 0 i).drop 0 i = (A.drop i i),
          { ext x y,
            by_cases hx : x = 0;
            by_cases hxi : x = i.pred (ne_of_gt hi),
            { rw [hx, drop_zero_row, minor, ←hx, hxi],
              simp [minor],
            },
            -- { simp [hxi, minor], },
            -- by_cases hxj : x = j',
            -- { simp [hxj, minor] },
            -- { rw swap_row_ne_apply _ _ _ _ _ hxi hxj,
            --   rw fin.pred_succ_iff at hxi hxj,
            --   simp only [minor, drop_zero_row, swap_row_ne_apply,
            --               hxi, hxj, ne.def, not_false_iff] }
                          },
         simp, },
      { sorry },
    },
  },
end


end det
