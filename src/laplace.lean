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

open_locale big_operators matrix

variables {R : Type*} [field R]
variables {n m : ℕ}

open matrix

section det

variables (A B : matrix (fin (n + 2)) (fin (n + 2)) R)

-- def det'' {R : Type*} [field R] :
--     Π {n : ℕ}, matrix (fin n) (fin n) R -> fin n -> R
-- | 0 _ _ := 1
-- | 1 M i := M i i
-- | (n + 2) M ⟨0, h⟩ := ∑ j, (M 0 j * (-1 : R) ^ (j.val) * det' (drop M 0 j) 0)
-- | (n + 2) M ⟨k + 1, hk⟩ := ∑ j, (M ⟨k + 1, hk⟩ j * (-1 : R) ^ (k + 1 + j.val) * det' (drop M ⟨k + 1, hk⟩ j)
--       ⟨k, (add_lt_add_iff_right 1).mp hk⟩)

def det' {R : Type*} [field R] :
    Π {n : ℕ}, matrix (fin n) (fin n) R -> fin n -> R
| 0 _ _ := 1
| 1 M i := M i i
| (n + 2) M i := dite (i = 0)
  (λ h, ∑ j, (M 0 j * (-1 : R) ^ (j.val) * det' (drop M 0 j) 0))
  (λ h, ∑ j, (M i j * (-1 : R) ^ (i.val + j.val) * det' (drop M i j) (fin.pred i h)))

@[simp] lemma det_zero_eq_one (A : matrix (fin 0) (fin 0) R) {i} : det' A i = 1 := rfl

@[simp] lemma det_one_eq_elem (A : matrix (fin 1) (fin 1) R) {i} : det' A i = A i i := rfl

lemma det_laplace_def (i) : det' A i = dite (i = 0)
  (λ h, ∑ j, (A 0 j * (-1 : R) ^ (j.val) * det' (drop A 0 j) 0))
  (λ h, ∑ j, (A i j * (-1 : R) ^ (i.val + j.val) * det' (drop A i j) (fin.pred i h))) := rfl

lemma det_laplace_z : det' A 0 = ∑ j, (A 0 j * (-1 : R) ^ (j.val) * det' (drop A 0 j) 0) := rfl

lemma det_laplace_nz (i : fin (n + 2)) (h : i ≠ 0) :
  det' A i = ∑ j, (A i j * (-1 : R) ^ (i.val + j.val) * det' (drop A i j) (fin.pred i h)) :=
by { rw det_laplace_def, exact dif_neg h }

lemma det_laplace_zero :
  det' A 0 = ∑ j, (A 0 j * (-1 : R) ^ (j.val) * det' (drop A 0 j) 0) := rfl

lemma det_laplace_zero' :
  det' A ⟨0, nat.succ_pos (n + 1)⟩ = ∑ j, (A 0 j * (-1 : R) ^ (j.val) * det' (drop A 0 j) 0) := rfl

lemma det_laplace_nonzero {i} (h : i + 1 < n + 2) :
  det' A ⟨i + 1, h⟩ = ∑ j, (A ⟨i + 1, h⟩ j * (-1 : R) ^ (i + 1 + j.val) * det' (drop A ⟨i + 1, h⟩ j)
      ⟨i, (add_lt_add_iff_right 1).mp h⟩) := rfl

lemma det_laplace_nonzero' {i : fin (n + 1)} :
  det' A i.succ = ∑ j, (A i.succ j * (-1 : R) ^ (i.val + 1 + j.val) * det' (drop A i.succ j) i) :=
begin
  cases i with i h,
  rw <-add_lt_add_iff_right 1 at h,
  exact det_laplace_nonzero A h,
end

-- lemma det_laplace_nonzero'' (i : fin (n + 1)) :
--   det' A (i + 1) = ∑ j, (A (i + 1) j * (-1 : R) ^ (i.val + 1 + j.val) * det' (drop A (i + 1) j) i) :=
-- by { simp }

instance fin_inhabited {n : ℕ} : inhabited (fin (n + 1)) := ⟨0⟩

@[simp] lemma fin.default_eq_zero {n : ℕ} : default (fin (n + 1)) = 0 := rfl

@[simp] lemma fin.default_succ_eq_one {n : ℕ} : fin.succ (default (fin (n + 1))) = 1 := rfl

lemma det_eq_det_dim2 (A : matrix (fin 2) (fin 2) R) (i j) : det' A i = det' A j :=
begin
  wlog hl : i ≤ j,
  fin_cases i;
  fin_cases j,
  { simp [det_laplace_z, det_laplace_nz, fin.zero_ne_one.symm, fin.one_pos, fin.succ_above_below, minor, fin.sum_univ_succ],
    ring },
  { exact absurd nat.one_pos (not_lt_of_le (fin.le_iff_val_le_val.mp hl)) }
end

lemma det_swap_eq_neg_det_dim2 (A : matrix (fin 2) (fin 2) R) (i j) (h : i ≠ j) : det' (swap_row A j i) j = - det' A j :=
begin
  wlog hl : i ≤ j,
  fin_cases i;
  fin_cases j,
  any_goals { contradiction },
  { simp [det_laplace_z, det_laplace_nz, minor, fin.sum_univ_succ, h.symm, fin.succ_above_below, fin.one_pos],
    ring },
  { exact absurd nat.one_pos (not_lt_of_le (fin.le_iff_val_le_val.mp hl)) },
  { rw [det_eq_det_dim2 A j i, ←this h.symm, swap_row_symmetric, det_eq_det_dim2 _ i j] }
end

example (f : fin 3 → ℕ) (g : fin 3 → ℕ) (h : f = g) : ∑ k, f k = ∑ l, g l := congr_arg finset.univ.sum h

lemma det_eq_det_at01 (A : matrix (fin (n + 2)) (fin (n + 2)) R) : det' A 1 = det' A 0 :=
begin
  induction n with n hn,
  { exact det_eq_det_dim2 A 1 0 },
  {
    have s1 : ∀ ix : fin (n + 1), fin.succ_above (1 : fin (n + 3)) ix.succ = ix.succ.succ,
      { intro ix, rw [fin.succ_above_above], simp [fin.le_iff_val_le_val, nat.succ_le_succ_iff] },
    -- rw det_laplace_z,
    rw det_laplace_nz _ _ (fin.zero_ne_one.symm),
    -- rw fin.sum_univ_succ,
    rw fin.sum_univ_succ_above _ (1 : fin (n + 3)),
    -- rw fin.sum_univ_succ_above _ (0 : fin (n + 3)),
    rw fin.pred_one,
    rw det_laplace_z,
    rw fin.sum_univ_succ,
    rw @fin.sum_univ_succ _ _ (n + 1),
    symmetry,
    rw det_laplace_z,
    rw fin.sum_univ_succ,
    rw det_laplace_z,
    rw fin.sum_univ_succ,
    simp [minor, fin.succ_above_below, fin.one_pos, s1, mul_add, add_assoc],
    congr' 1,
    { ring },
    simp [fin.sum_univ_succ, det_laplace_z, ←hn],
    -- congr' 1,
    -- rw [fin.pred_one, det_laplace_z, det_laplace_z],
    -- rw [fin.sum_univ_succ, @fin.sum_univ_succ _ _ (n + 1), mul_add, mul_add],
    -- congr' 1,
    -- {
    --   simp [minor, fin.succ_above_below, fin.one_pos, s1],
    --   ring },
    -- {
    --   rw [fin.sum_univ_succ, fin.sum_univ_succ, mul_add, mul_add],
    --   simp [minor, fin.succ_above_below, fin.one_pos, s1],
    -- },
    -- simp [minor, det_laplace_z, fin.succ_above_below, fik.one_val, fin.sum_univ_succ],
  }
end

#exit

lemma det_swap_eq_neg_det_dim3 (A : matrix (fin (n + 2)) (fin (n + 2)) R) : det' (swap_row A 0 1) 1 = - det' A 0 :=
begin
  induction n with n hn,
  { rw det_eq_det_dim2 _ 1 0,
    exact det_swap_eq_neg_det_dim2 A 1 0 (fin.zero_ne_one.symm) },
  {
    have s01' : ∀ ix : fin (n + 1), ∀ jx : fin (n + 3), swap_row A 0 1 ix.succ.succ jx = A ix.succ.succ jx,
      { intros ix jx, rw [swap_row_ne_apply], exact fin.succ_ne_zero _, exact fin.succ_succ_ne_one },
    have s1 : ∀ ix : fin (n + 1), fin.succ_above (1 : fin (n + 3)) ix.succ = ix.succ.succ,
      { sorry },
    have n1 : ∀ n, (-1 : R) ^ ((1 : fin (n + 2)).val) = -1 := by simp,
    have n0 : ∀ n, (-1 : R) ^ ((0 : fin (n + 1)).val) = 1 := by simp,
    symmetry,
    -- rw det_laplace_z,
    -- rw ←finset.sum_neg_distrib,
    -- rw det_laplace_z,
    -- congr,
    -- ext k,
    -- convert_to A 0 k * (-1) ^ (k.val + 1) * det' (A.drop 0 k) 0 = _,
    -- ring_exp,
    -- rw det_laplace_z,
    -- rw det_laplace_z,
    -- rw finset.mul_sum,
    -- rw finset.mul_sum,
    -- congr,
    -- ext l,
    -- convert_to A 0 k * A 1 (k.succ_above l) * (-1) ^ (k.val + l.val + 1) * det' ((A.drop 0 k).drop 0 l) 0 = _,
    -- ring_exp,
    -- simp [minor, s01'],
    -- ring_exp,
    -- revert l,
    -- refine congr_fun _,
    -- apply finset.sum_congr,
    -- revert k,
    -- refine congr_fun _,
    have key : ∀ k : fin (n + 3), ∀ l : fin (n + 2), ∀ x : R,
      (-1) ^ (k.val + 1) * A 0 k * A.drop 0 k 0 l * (-1) ^ (l.val) * x =
      (A 0 k * (-1) ^ (k.val + 1)) * (A.drop 0 k 0 l * (-1) ^ (l.val + 1)) * -x,
      { intros k l x, ring_exp },
    have drop_swap : ∀ k : fin (n + 3), ∀ l : fin (n + 2),
      (A 0 k * (-1) ^ (k.val + 1)) * (A.drop 0 k 0 l * (-1) ^ (l.val + 1)) =
      ((A.swap_row 0 1) 1 k * (-1) ^ (k.val + 1)) * ((A.swap_row 0 1).drop 1 k 0 l * (-1) ^ (l.val + 1)),
      { intros k l, simp [minor, fin.succ_above_below, fin.one_pos, mul_comm] },
    calc
    - det' A 0 = - ∑ k : fin (n + 3), A 0 k * _ * _ : by rw det_laplace_z
    ...        = ∑ k : fin (n + 3), - (A 0 k * _ * det' (A.drop 0 k) 0) : by rw ←finset.sum_neg_distrib
    ...        = ∑ k : fin (n + 3), (-1) ^ (k.val + 1) * A 0 k * det' (A.drop 0 k) 0 : by { ring_exp }
    ...        = ∑ k : fin (n + 3), (-1) ^ (k.val + 1) * A 0 k * (∑ l : fin (n + 2), A.drop 0 k 0 l * (-1) ^ (l.val) * _) : by simp_rw det_laplace_z
    ...        = ∑ k : fin (n + 3), (-1) ^ (k.val + 1) * (∑ l : fin (n + 2), A 0 k * A.drop 0 k 0 l * (-1) ^ (l.val) * _) : by simp_rw [mul_assoc, finset.mul_sum]
    ...        = ∑ k : fin (n + 3), (∑ l : fin (n + 2), (-1) ^ (k.val + 1) * A 0 k * A.drop 0 k 0 l * (-1) ^ (l.val) * _) : by simp_rw [finset.mul_sum, ←mul_assoc]
    ...        = ∑ k : fin (n + 3), (∑ l : fin (n + 2), ((A.swap_row 0 1) 1 k * (-1) ^ (k.val + 1)) * (((A.swap_row 0 1).drop 1 k 0 l * (-1) ^ (l.val + 1)) * -_)) : by simp_rw [key, drop_swap, mul_assoc]
    ...        = ∑ k : fin (n + 3), ((A.swap_row 0 1) 1 k * (-1) ^ (k.val + 1)) * (∑ l : fin (n + 2), ((A.swap_row 0 1).drop 1 k 0 l * (-1) ^ (l.val + 1)) * -det' ((A.drop 0 k).drop 0 l) 0) : by { simp_rw [←finset.mul_sum] }
    ...        = ∑ k : fin (n + 3), ((A.swap_row 0 1) 1 k * (-1) ^ (k.val + 1)) * (∑ l : fin (n + 2), ((A.swap_row 0 1).drop 1 k 0 l * (-1) ^ (l.val + 1)) * _) : by simp_rw [←finset.mul_sum]
    ...        = det' (swap_row A 0 1) 1 : by { sorry }
    -- det' (swap_row A 0 1) 0 = ∑ x : fin (n + 3), _ * _ * _ : by rw det_laplace_z
    -- ...                     = _ * _ * _ + ∑ x : fin (n + 2), _ * _ * _ : by rw fin.sum_univ_succ
    -- ...                     = - det' A 0 : by { sorry },
    -- simp [det_laplace_z, s01', s1] at hn,
    -- simp [det_laplace_z, fin.sum_univ_succ, minor, s01', s1, n1, n0],
    -- rw det_laplace_z,
    -- congr,
    -- ext I,
    -- rw det_laplace_z,
    -- rw finset.mul_sum,
    -- rw det_laplace_z,
    -- rw finset.mul_sum,
    -- rw ←finset.sum_neg_distrib,
    -- congr,
    -- ext J,
    -- simp [minor, s01'],
    -- ring,
    -- rw fin.sum_univ_succ,
    -- rw fin.sum_univ_succ,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- rw mul_add,
    -- rw det_laplace_z,
    -- rw @fin.sum_univ_succ _ _ (n + 1),
    -- rw mul_add,
    -- symmetry,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- rw fin.sum_univ_succ,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- rw mul_add,
    -- rw det_laplace_z,
    -- rw @fin.sum_univ_succ _ _ (n + 1),
    -- rw mul_add,
    -- simp [pow_add, pow_succ, s01', s1, minor, fin.succ_above_below, fin.one_pos, neg_mul_eq_neg_mul_symm, fin.val_zero', mul_one,
    -- fin.cast_succ_zero, swap_row_swap_apply, drop_zero_row_column, pow_one, mul_neg_eq_neg_mul_symm, fin.succ_zero_eq_one,
    -- fin.succ_val, swap_row_apply, neg_neg, fin.val_one, drop_zero_row, pow_zero, fin.succ_above_zero],
    -- rw det_laplace_z,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
  -- rw mul_add,
    -- rw add_comm,
    -- rw fin.sum_univ_succ,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- rw mul_add,
    -- simp [-det_laplace_z, minor, s01', fin.one_pos, fin.succ_above_below, s1, pow_succ, pow_add],
    -- rw neg_mul_eq_neg_mul,
    -- rw add_add_add_comm,
    -- rw add_assoc,
    -- rw add_assoc,
    -- rw add_comm ((A 1 1 * _)),
    -- rw ←mul_assoc,
    -- rw ←mul_assoc,
    -- rw ←add_assoc,
    -- rw ←add_assoc,
    -- rw mul_comm,
    -- rw mul_assoc,
    -- rw mul_comm (A 0 1),
    -- rw ←mul_left_comm (det' _ 0),
    -- rw ←mul_add,
    -- rw add_assoc,
    -- rw finset.mul_sum,
    -- rw finset.mul_sum,
    -- rw ←finset.sum_neg_distrib,
    -- rw ←finset.sum_add_distrib,
    -- rw ←finset.sum_add_distrib,
    -- symmetry,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- rw neg_add',
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- simp [-det_laplace_z, minor, s01', fin.one_pos, fin.succ_above_below, s1],
    -- rw mul_add,
    -- rw add_comm,
    -- rw fin.sum_univ_succ,
    -- rw det_laplace_z,
    -- rw fin.sum_univ_succ,
    -- rw mul_add,
    -- simp [-det_laplace_z, minor, s01', fin.one_pos, fin.succ_above_below, s1],
    -- rw neg_mul_eq_neg_mul,
    -- rw add_add_add_comm,
    -- rw add_assoc,
    -- rw add_assoc,
    -- rw add_comm (-(A 1 1 * _)),
    -- rw ←mul_assoc,
    -- rw ←mul_assoc,
    -- rw ←add_assoc,
    -- rw ←add_assoc,
    -- rw mul_comm,
    -- rw mul_assoc,
    -- rw mul_comm (A 0 1),
    -- rw ←mul_left_comm (det' _ 0),
    -- rw ←mul_add,
    -- rw add_assoc,
    -- rw finset.mul_sum,
    -- rw finset.mul_sum,
    -- rw ←finset.sum_add_distrib,
    -- rw ←finset.sum_neg_distrib,
    -- rw ←finset.sum_add_distrib,
    -- {  },
      -- rw fin.sum_univ_succ,
      -- rw @fin.sum_univ_succ _ _ (n + 1),
      -- rw det_laplace_z,
      -- rw fin.sum_univ_succ,
      -- rw det_laplace_z,
      -- rw @fin.sum_univ_succ _ _ (n + 1),
      -- simp [minor, s01', fin.one_pos, fin.succ_above_below, pow_add, pow_succ, fin.val_one],
    {  },
    {  },
  },

end

#exit

example {n' : ℕ} (i' j' : fin n') (A' : matrix (fin n') (fin n') R) : j' < i' → - det' (swap_row A' j' i') j' = det' A' j' :=
fin.succ_rec_on i'
(λ n j A h, by { exact absurd h (not_lt_of_le (fin.zero_le j)) })
(λ n i IH j A, by {
  clear A' i' j' n',
  rcases n with _|_|n,
  { exact fin_zero_elim i },
  { intro h,
    exact det_swap_eq_neg_det_dim2 _ _ _ (ne_of_gt h), },
  intro h,
  obtain ⟨i, hi⟩ := i,
  obtain ⟨j, hj⟩ := j,
  induction i with i HI,
  { simp at h,
    have j0 : j = 0,
      { rw [fin.lt_iff_val_lt_val, fin.val_one] at h, cases j, refl, exact absurd (nat.lt_of_succ_lt_succ h) (not_lt_of_le (nat.zero_le j)) },
    have J0 : (⟨j, hj⟩ : fin (n + 3)) = 0 := fin.eq_of_veq j0,
    have n01 : (0 : fin (n + 3)) ≠ 1 := ne_of_lt (fin.succ_pos 0),
    have n11 : (1 : fin (n + 3)) ≠ fin.succ 1,
      { refine fin.ne_of_vne _, rw [fin.succ_val, fin.val_one, fin.val_one], exact ne.symm (nat.succ_ne_self 1) },
    have n0 : ∀ {ix : ℕ}, ∀ {ix_is_lt : ix.succ < n + 2}, (1 : fin (n + 3)).succ_above ⟨ix.succ, ix_is_lt⟩ ≠ 0,
      { intros ix h,
        refine ne_of_gt _,
        refine fin.succ_above_pos 1 _ _,
        simp [fin.lt_iff_val_lt_val] },
    have s01 : ∀ ix : fin (n + 2), ∀ jx : fin (n + 3), swap_row A 0 1 (fin.succ_above 1 ix) jx = A ix.succ jx,
      { intros ix jx,
        rcases ix with _|ix,
        { simp [fin.succ_above_below, fin.one_pos] },
        { rw [swap_row_ne_apply _ _ _ _ _ n0 (fin.succ_above_ne _ _), fin.succ_above_above],
          simp [nat.succ_le_succ_iff] } },
    have s01' : ∀ ix : fin (n + 1), ∀ jx : fin (n + 3), swap_row A 0 1 ix.succ.succ jx = A ix.succ.succ jx,
      { intros ix jx, rw [swap_row_ne_apply], exact fin.succ_ne_zero _, exact fin.succ_succ_ne_one },
    rw [J0, det_laplace_z, det_laplace_z,
        fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_succ],
    -- simp [J0, fin.sum_univ_succ, minor, pow_add, s01'],
    },
--   {
--     -- have key : ∀
-- --     -- cases n,
-- --     -- { cases i, exact absurd hi (lt_irrefl 1), exact absurd (nat.lt_of_succ_lt_succ hi) (not_lt_of_le (nat.zero_le i.succ)) },
-- --     induction j with j HJ,
-- --     {
-- --       rw ←swap_row_thrice _ _ 1,
-- --       rw fin.mk_zero_eq_zero,
-- --       rw det_laplace_z,
-- --       rw det_laplace_nz,
-- --       simp only [fin.sum_univ_succ, pow_add, pow_succ, add_comm, neg_mul_eq_neg_mul_symm, fin.zero_val, mul_one, one_mul, fin.pred_succ,
-- --  mul_neg_eq_neg_mul_symm, fin.succ_zero_eq_one, neg_add_rev, fin.succ_val, neg_neg, pow_zero],
-- --       congr,
-- --       rw swap_row_thrice _ _ 1,
-- --       rw neg_mul_eq_mul_neg,
-- --       rw mul_assoc,
-- --       congr,
-- --       { simp },
-- --       { rw det_laplace_nz,
-- --         rw fin.sum_univ_succ,
-- --         simp [-drop_def, -drop_zero_row, -drop_zero_column],
-- --       },

-- --     },
-- --     {  },
--   }
}) j' A'


example {n' : ℕ} (i' j' : fin n') (A' : matrix (fin n') (fin n') R) : i' < j' → - det' (swap_row A' j' i') i' = det' A' j' :=
fin.succ_rec_on i'
(λ n j A h, by {
  clear A' i' j' n',
  induction n with n hn,
  { rw (show (0 : fin 1) = fin.last 0, by refl) at h,
    exact absurd h (not_lt_of_le (fin.le_last _)) },
  {
    obtain ⟨j, hj⟩ := j,
    rcases j with _|j,
    { rw [fin.mk_zero] at h,
      exact absurd h (lt_irrefl 0) },
    induction j with j JH,
    {
      sorry,
      -- rw [det_laplace_z, fin.sum_univ_succ, fin.sum_univ_succ,
      --     fin.mk_one_eq_one, det_laplace_nz _ _ fin.zero_ne_one.symm,
      --     fin.sum_univ_succ, fin.sum_univ_succ, neg_add],
      -- have drop_swap : ∀ x, drop (swap_row A 0 1) 1 x = drop A 0 x,
      --   by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
      -- simp [drop_swap, add_comm, fin.sum_univ_succ, pow_add],
    },
    {
      set J := (⟨j, nat.lt_of_succ_lt_succ (nat.lt_of_succ_lt_succ hj)⟩ : fin n) with hJ,
      have ne0_J' : J.succ ≠ 0 := fin.ne_of_vne (ne_of_gt (nat.succ_pos j)),
      have ne0_J'' : J.succ.succ ≠ 0 := fin.ne_of_vne (ne_of_gt (nat.succ_pos j.succ)),
      have hJ' : J.succ = ⟨j.succ, nat.lt_of_succ_lt_succ hj⟩ := rfl,
      have hJ'' : J.succ.succ = ⟨j.succ.succ, hj⟩ := rfl,
      rw det_laplace_z,
      rw fin.sum_univ_succ,
      rw ←hJ'',
      rw det_laplace_nz _ _ ne0_J'',
      rw fin.sum_univ_succ,
      simp [fin.sum_univ_succ, pow_add, pow_succ, add_comm, ne0_J', minor],
      congr,
      {
        have pos_J' : 0 < J.succ := fin.lt_iff_val_lt_val.mpr (nat.succ_pos j),
        have Jpred : J.succ.succ.pred ne0_J'' = J.succ := rfl,
        rw neg_mul_eq_mul_neg,
        rw mul_assoc,
        rw ←hn J.succ _ pos_J',
        congr,
        rw det_laplace_z,
        have ne0_J' : J.succ ≠ 0 := fin.ne_of_vne (ne_of_gt (nat.succ_pos j)),
        have ne0_csJ' : J.succ.cast_succ ≠ 0 := fin.ne_of_vne (ne_of_gt (nat.succ_pos j)),
        have neJ_J' : J.succ.cast_succ ≠ J.succ.succ := (ne_of_lt (cast_succ_lt_succ J.succ)),
        cases n,
        { exact absurd (zero_le _) (not_le_of_lt (nat.lt_of_succ_lt_succ (nat.lt_of_succ_lt_succ hj))), },
        have swap_ne : ∀ p k x, swap_row A p 0 (p.succ_above (fin.succ k)) x = A (p.succ_above k.succ) x,
          { intros p k x,
            rw swap_row_ne_apply,
            { exact fin.succ_above_ne p k.succ },
            { refine (ne_of_gt (succ_above_pos _ _ (fin.lt_iff_val_lt_val.mpr _))),
              simp only [fin.zero_val, fin.succ_val, nat.succ_pos] },
          },
        rw det_laplace_nz _ J.succ (ne_of_gt pos_J'),
        rw det_laplace_nz _ J.succ (ne_of_gt pos_J'),
        rw fin.sum_univ_succ,
        simp [swap_ne],
        rw fin.sum_univ_succ,
        rw fin.sum_univ_succ,
        rw fin.sum_univ_succ,
        have pJ : J.succ.pred (ne_of_gt pos_J') = J := rfl,
        -- simp [fin.sum_univ_succ, minor, swap_ne, Jpred, pos_J', ne0_J', ne0_csJ', neJ_J', pJ, pow_add, add_comm, mul_comm],
      },
     }
  }
  })
(λ n i IH j A, by {
  sorry,
}) j' A'

lemma det_swap_match_eq_neg_det' (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i j) (h : i ≠ j) : det' (swap_row A i j) i = - det' A 0 :=
begin
  induction n with n hn,
    { rw det_eq_det_dim2 _ i 0,
      exact det_swap_eq_neg_det_dim2 A i j h },
    {
      wlog hl : j < i using [i j, j i],
      { rcases lt_trichotomy j i with H|rfl|H,
        { exact or.inl H },
        { contradiction },
        { exact or.inr H } },
      { obtain ⟨i, hi⟩ := i,
        obtain ⟨j, hj⟩ := j,
        induction i with i IH,
          { induction j with j JH,
            { contradiction },
            { exact absurd (zero_le j.succ) (not_le_of_lt hl) } },
          { induction j with j HJ,
            {
              rcases i with _|i,
              {
                sorry
              },
              {
                specialize HI (nat.succ_pos i) (nat.lt_of_succ_lt hi) (fin.ne_of_vne (nat.succ_ne_zero i)),
                set I : fin (n + 2) := ⟨i.succ, (add_lt_add_iff_right 1).mp hi⟩,
                have sI : I.succ = ⟨i.succ.succ, hi⟩, by simp [fin.eq_iff_veq],
                have ne0 : I ≠ 0 := fin.ne_of_vne (nat.succ_ne_zero i),
                have gt0 : 0 < I := fin.lt_iff_val_lt_val.mpr (nat.succ_pos i),
                have pI : I.pred ne0 = ⟨i, (add_lt_add_iff_right 2).mp hi⟩, by simp [fin.eq_iff_veq],
                have saI : ∀ k, I.succ.succ_above k ≠ I.succ := λ k, fin.succ_above_ne I.succ k,
                have sa0 : ∀ {ih : i + 1 < n + 2}, I.succ.succ_above ⟨i + 1, _⟩ ≠ 0,
                  { intros ih H,
                    rw fin.succ_above at H,
                    split_ifs at H,
                    simpa [fin.eq_iff_veq] using H,
                    exact fin.succ_ne_zero ⟨i + 1, ih⟩ H },
                have swI : ∀ k, ∀ (hk : 0 < k), ∀ (ih : i + 1 < n + 2), ∀ col, swap_row A I.succ 0 (I.succ.succ_above k) col = ite (k.val < I.succ.val) (A k.cast_succ col) (A k.succ col),
                  { intros k hk ih col,
                    rw swap_row_ne_apply,
                    split_ifs with H,
                    { simp [H] },
                    { simp [not_lt.mp H] },
                    { exact fin.succ_above_ne _ _ },
                    { exact (ne_of_gt (succ_above_pos _ _ hk)) },
                    },
                simp only [←sI],
                rw [det_laplace_z, fin.sum_univ_succ, fin.val_zero, pow_zero, mul_one, neg_add],
                rw [det_laplace_nz, fin.sum_univ_succ, swap_row_swap_apply, fin.mk_zero_eq_zero, fin.val_zero, pow_add, pow_zero, mul_one, neg_mul_eq_mul_neg, mul_assoc],
                congr,
                rw [fin.pred_succ, det_laplace_nz _ _ ne0, finset.mul_sum, fin.sum_univ_succ, ←hn _ I 0 ne0],
                rw [det_laplace_nz _ _ ne0, @fin.sum_univ_succ _ _ (n + 1)],
                simp [pow_add, minor, pI],
                rw swI _ gt0 (nat.lt_of_succ_lt_succ hi),
                rw if_pos,
                -- simp,
                -- -- simp [saI, sa0, ne0, minor],
                -- -- rw swap_row_ne_apply,
                -- -- rw succ_above_below,
                -- -- , det_laplace_z, ←finset.sum_neg_distrib],
                -- congr,
                -- ext x,
                -- have : drop (swap_row A I.succ 0) I.succ 0 I x = drop A 0 0 0 x,
                --   { simp [minor], rw swap_row_ne_apply, },
                -- simp [HI, sa0, saI, minor, pow_add, add_comm, mul_comm],
                -- rw [det_laplace_nz, neg_mul_eq_mul_neg],
                -- convert_to A 0 0 * ((-1) ^ (I.val) * ∑ x, _) = _,
                -- {
                --   simp only [neg_mul_eq_neg_mul_symm, one_mul, pow_add, pow_succ, mul_neg_eq_neg_mul_symm, neg_inj, finset.sum_neg_distrib, neg_neg],
                --   rw <-mul_assoc,
                --   rw mul_comm (A 0 0),
                -- },
                -- congr,
                },
              },
              {  }
            },
        },
        {
      }
    }
end

        -- { rcases i with _|_|i,
        --   { contradiction },
        --   { exact absurd nat.one_pos (not_lt_of_le hl) },
        --   { exact absurd nat.succ_pos' (not_lt_of_le hl) } },
          -- { contradiction },
          -- { rw fin.mk_zero_eq_zero at h,
          --   rw [det_laplace_z, fin.sum_univ_succ, fin.sum_univ_succ,
          --       det_laplace_nz _ _ h.symm, fin.sum_univ_succ, fin.sum_univ_succ],
          --   have drop_swap : ∀ x, drop (swap_row A 0 1) 1 x = drop A 0 x,
          --     by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
          --   simp [drop_swap, add_comm, pow_add] },
      --   rcases j with _|j,
      --   { rcases i with _|_|i,
      --     { contradiction },
      --     { exact absurd nat.one_pos (not_lt_of_le hl) },
      --     { exact absurd nat.succ_pos' (not_lt_of_le hl) } },
      --   { induction j with j JH,
      --     { rcases i with _|_|i,
      --       { rw fin.mk_zero_eq_zero at h,
      --         rw [det_laplace_z, fin.sum_univ_succ, fin.sum_univ_succ,
      --             det_laplace_nz _ _ h.symm, fin.sum_univ_succ, fin.sum_univ_succ],
      --         have drop_swap : ∀ x, drop (swap_row A 0 1) 1 x = drop A 0 x,
      --           by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
      --         simp [drop_swap, add_comm, pow_add] },
      --       { contradiction },
      --       { exact absurd (nat.succ_lt_succ nat.succ_pos') (not_lt_of_le hl) } },
      --     { rcases i with _|i,
      --       {  },
      --       {  },
      --      }
      --      },
      --     {  },
      -- },
      -- {

      -- }

lemma det_swap_match_eq_neg_det (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i j) (h : i ≠ j) : det' (swap_row A i j) j = - det' A 0 :=
begin
  by_cases H : i = j,
  { contradiction },
  clear H,
  induction n with n hn;
  obtain ⟨i, hi⟩ := i;
  obtain ⟨j, hj⟩ := j,
  have le_2 : ∀ k, 2 ≤ (nat.succ k).succ := λ k, inf_eq_left.mp rfl,
  -- induction i with i hi,
  -- { induction n with n hn,
  { rcases i with _|_|i,
    { rcases j with _|_|j,
      { contradiction },
      { have swap_01 : swap_row A ⟨0, hi⟩ ⟨1, hj⟩ 0 = A 1 := rfl,
        rw det_laplace_nonzero,
        simp [minor, fin.sum_univ_succ, swap_01],

        ring },
      { norm_num at hj,
        exfalso,
        linarith [le_2 j, hj] } },
    { rcases j with _|_|j,
      { simp [minor, fin.sum_univ_succ, fin.succ_above_below, fin.one_pos],
        ring },
      { contradiction },
      { norm_num at hj,
        exfalso,
        linarith [le_2 j, hj] } },
    { norm_num at hi,
      exfalso,
      linarith [le_2 i, hi] } },
  have le_2 : ∀ k, 2 ≤ (nat.succ k).succ := λ k, inf_eq_left.mp rfl,
  {
    rcases i with _|_|i,
    -- { rcases j with _|j,
    --   { contradiction },
    --   induction j with j JH,
    --   {
    --     have drop_swap : ∀ x, drop (swap_row A ⟨0, hi⟩ ⟨1, hj⟩) ⟨1, hj⟩ x = drop A 0 x,
    --       by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
    --     have drop_swap' : ∀ x, drop (swap_row A 0 ⟨1, hj⟩) ⟨1, hj⟩ x = drop A 0 x := λ x, drop_swap x,
    --     simp [-fin.mk_one_eq_one, fin.sum_univ_succ, drop_swap, drop_swap', add_comm, mul_comm, pow_add] },
    --   {
    --     simp [add_comm, mul_comm, pow_add, minor, fin.sum_univ_succ],
    --     ring_exp,
    --     },
    --     -- norm_num at hj,
    --     -- exfalso,
    --     -- linarith [le_2 j, hj],
    --     } },
    -- {  },
    -- {  }
    },
end

lemma det_swap_match_eq_neg_det' (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i j) (h : i ≠ j) : det' (swap_row A i j) i = - det' A 0 :=
begin
  by_cases H : i = j,
  { contradiction },
  clear H,
  obtain ⟨i, hi⟩ := i,
  obtain ⟨j, hj⟩ := j,
  induction i with i IH,
  { rcases j with _|j,
    { contradiction },
    { induction j with j JH,
      {
        have le_2 : ∀ k, 2 ≤ (nat.succ k).succ := λ k, inf_eq_left.mp rfl,
        have drop_swap : ∀ x, drop (swap_row A 0 ⟨1, hj⟩) ⟨1, hj⟩ x = drop A 0 x,
          by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
        have drop_swap' : ∀ x, drop (swap_row A ⟨1, hj⟩ 0) 0 x = drop A 1 x,
          by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
        simp [minor, fin.sum_univ_succ, drop_swap, pow_add, drop_swap',
 neg_mul_eq_neg_mul_symm, one_mul, det_laplace_zero, det_laplace_nonzero, pow_one, mul_neg_eq_neg_mul_symm,
 finset.sum_neg_distrib, swap_row_apply],
        ring,
 },
        { sorry },
    },
  },
  { rcases j with _|j,
    {
      have s0 : ∀ n, (⟨0, nat.succ_pos'⟩ : fin (n + 1)) = 0 := λ n, rfl,
      -- have drop_swap : ∀ x, drop (swap_row A ⟨i.succ, hi⟩ 0) 0 x = drop A ⟨i.succ, hi⟩ x,
      --   by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
      -- have det_drop_swap : ∀ x ix jx, det' (drop (swap_row x 0) 0 jx) 0 =
      simp only [s0, fin.sum_univ_succ, pow_add, add_comm, mul_comm, neg_mul_eq_neg_mul_symm, fin.zero_val, nat.nat_zero_eq_zero,
 one_mul, det_laplace_zero, pow_one, neg_add_rev, fin.succ_val, swap_row_apply, neg_neg, pow_zero],
     },
    {  },
  },
--   induction i with i IH,
--   { rcases j with _|j,
--     { contradiction },
--     { induction j with j JH,
--       {
--         have s0 : ∀ n, (⟨0, nat.succ_pos'⟩ : fin (n + 1)) = 0 := λ n, rfl,
--         have succ_0 : ∀ n, (0 : fin (n + 1)).succ = 1 := λ n, rfl,
--         have le_2 : ∀ k, 2 ≤ (nat.succ k).succ := λ k, inf_eq_left.mp rfl,
--         have drop_swap : ∀ x, drop (swap_row A 0 ⟨1, hj⟩) ⟨1, hj⟩ x = drop A 0 x,
--           by { intro x, ext ii jj, rcases ii with ⟨⟨_⟩, _⟩; simpa },
--         simp only [s0, minor, fin.sum_univ_succ, drop_swap, pow_add,
--  neg_mul_eq_neg_mul_symm, one_mul, det_laplace_zero, det_laplace_nonzero, pow_one, mul_neg_eq_neg_mul_symm,
--  finset.sum_neg_distrib, swap_row_apply] },
--       {
--         have s0 : ∀ n, (⟨0, nat.succ_pos'⟩ : fin (n + 1)) = 0 := λ n, rfl,
--         have succ_0 : ∀ n, (0 : fin (n + 1)).succ = 1 := λ n, rfl,
--         have le_2 : ∀ k, 2 ≤ (nat.succ k).succ := λ k, inf_eq_left.mp rfl,
--         simp [s0, minor, fin.sum_univ_succ, pow_add,
--         neg_mul_eq_neg_mul_symm, one_mul, det_laplace_zero, det_laplace_nonzero, pow_one, mul_neg_eq_neg_mul_symm,
--         finset.sum_neg_distrib, swap_row_apply, add_comm, mul_comm],
--         ring,
--         } } },
end

lemma det_eq_det (A : matrix (fin n) (fin n) R) (i j) : det' A i = det' A j :=
begin
  induction n with n hn,
  { exact fin.elim0 i },
  cases n,
  { rw subsingleton.elim i j },
  refine fin.cases _ _ i;
  refine fin.cases _ _ j,
  { refl },
  { intros ix,
    },

end

end det
