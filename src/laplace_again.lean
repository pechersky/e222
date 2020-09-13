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

lemma pow_succ_above {n : ℕ} (x : fin (n + 1)) (y : fin n) : (-1 : R) ^ ((x.succ_above y).val) = ite (y.cast_succ < x) ((-1) ^ (y.val)) ((-1) ^ (y.val + 1)) :=
begin
  unfold fin.succ_above,
  split_ifs;
  simp
end

lemma test2 (x : fin (n + 1)) (y : fin n) : (-1 : R) ^ (x : ℕ) * (-1) ^ ((x.succ_above y) : ℕ)
  = (-1) ^ ((x + y) : ℕ) * ite (y.cast_succ < x) 1 (-1) :=
begin
  cases (fin.succ_above_lt_ge x y) with h h,
  { rw [fin.succ_above_below _ _ h, if_pos h],
    rw [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ] at h,
    simp only [pow_add, mul_one, fin.coe_cast_succ] },
  { rw [fin.succ_above_above _ _ h, if_neg (not_lt_of_le h)],
    rw [fin.le_iff_coe_le_coe, fin.coe_cast_succ] at h,
    simp only [pow_add, mul_one, fin.coe_succ, pow_one, mul_neg_eq_neg_mul_symm] }
end

lemma test3 (x : fin (n + 1)) (y : fin n) : (-1 : R) ^ ((x + y) : ℕ) =
 (-1 : R) ^ (x : ℕ) * (-1) ^ ((x.succ_above y) : ℕ) * ite (x.succ_above y ≤ x) 1 (-1) :=
begin
  unfold fin.succ_above,
  split_ifs with h H H h,
  { simp only [mul_one, fin.coe_cast_succ],
    ring_exp },
  { exact absurd (le_of_lt h) H },
  { exact absurd (lt_of_lt_of_le (fin.cast_succ_lt_succ y) H) h },
  { simp only [mul_one, fin.coe_succ],
    ring_exp }
end

lemma test4 (f : fin (n + 2) → R) (x : fin (n + 2)) : (∑ y : fin (n + 1), f (x.succ_above y)) = ∑ y, ite (x ≠ y) (f y) 0 :=
begin
  symmetry,
  rw fin.sum_univ_succ_above _ x,
  simp,
  congr' 1 with y,
  rw if_pos (fin.succ_above_ne x y).symm,
end

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp] lemma fin.succ_above_lt_iff (p : fin (n + 1)) (i : fin n) : p.succ_above i < p ↔ i.cast_succ < p :=
begin
  refine iff.intro _ _,
  { intro h,
    cases fin.succ_above_lt_ge p i with H H,
    { exact H },
    { rw fin.succ_above_above _ _ H at h,
      exact lt_trans (fin.cast_succ_lt_succ i) h } },
  { intro h,
    rw fin.succ_above_below _ _ h,
    exact h }
end

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
lemma fin.lt_succ_above_iff (p : fin (n + 1)) (i : fin n) : p < p.succ_above i ↔ p ≤ i.cast_succ :=
begin
  refine iff.intro _ _,
  { intro h,
    cases fin.succ_above_lt_ge p i with H H,
    { rw fin.succ_above_below _ _ H at h,
      exact le_of_lt h },
    { exact H } },
  { intro h,
    rw fin.succ_above_above _ _ h,
    exact lt_of_le_of_lt h (fin.cast_succ_lt_succ i) },
end

example (f : fin n → fin n → ℕ) : (∑ x, ∑ y, f x y) = ∑ x, ∑ y, f y x :=
finset.sum_comm

example (x : fin (n + 2)) (y : fin (n + 1)) (j : fin n) :
  x.succ_above (y.succ_above j) = let y' := x.succ_above y in dite (y' = x) (λ _, j.succ.succ) (λ h, x.succ_above ((x.pred_above y' h).succ_above j)) :=
begin
  simp only [dif_neg (x.succ_above_ne y)],
  simp only [fin.pred_above_succ_above],
end

example (m n : ℕ) (hpos : 0 < n) (h : m < n - 1) : n - 1 ≤ n := nat.sub_le n 1

example (m n : ℕ) (hpos : 0 < n) (h : m < n - 1) : m < n := lt_of_lt_of_le h (nat.sub_le n 1)

example (m n : ℕ) (hpos : 0 < n) (h : m < n) : m ≤ n - 1 := nat.le_pred_of_lt h

example (m n : ℕ) (hpos : 0 < n) (h : n - 1 < m) : n < m + 1 := by { exact nat.lt_add_of_sub_lt_right h}

example (m n : ℕ) (hpos : 0 < n) (h : n - 1 < m) (h' : n < m + 1) : n ≤ m := by { exact nat.lt_succ_iff.mp h' }

lemma nat.pred_lt_le {m n : ℕ} (h : n - 1 < m) : n ≤ m := nat.le_of_succ_le_succ (nat.lt_add_of_sub_lt_right h)

-- lemma nat.pred_le {m n : ℕ} (h : n - 1 < m) : n ≤ m := nat.le_of_succ_le_succ (nat.lt_add_of_sub_lt_right h)

-- #check nat.pred_le_lt {m n : ℕ} (h : n - 1 ≤ m) :

example {m n : ℕ} (h : n - 1 ≤ m) (H : m < n) : n - 1 = m := by { exact le_antisymm h (nat.le_pred_of_lt H) }

example {m n : ℕ} (h : n - 1 < m) (H : m < n) : false := by { exact absurd (nat.pred_lt_le h) (not_le_of_lt H) }

example {m n : ℕ} (h : n < m - 1) : n + 1 < m  := by {exact nat.add_lt_of_lt_sub_right h}

example (x : fin (n + 2)) (y : fin (n + 1)) (j : fin n) : ((x.succ_above y).pred_above x (ne.symm (fin.succ_above_ne _ _))) = y :=
begin
  unfold fin.succ_above,
  unfold fin.pred_above,
  split_ifs,
end

lemma fin.cast_succ_lt_iff (x y : fin n) : x.cast_succ < y.cast_succ ↔ x < y :=
begin
  rw [fin.lt_iff_coe_lt_coe, fin.lt_iff_coe_lt_coe],
  exact iff.rfl
end

lemma fin.cast_succ_le_iff (x y : fin n) : x.cast_succ ≤ y.cast_succ ↔ x ≤ y :=
begin
  rw [fin.le_iff_coe_le_coe, fin.le_iff_coe_le_coe],
  exact iff.rfl
end

lemma fin.le_succ_above (p : fin (n + 1)) (i : fin n) : i.cast_succ ≤ p.succ_above i :=
begin
  cases fin.succ_above_lt_ge p i,
  { rw fin.succ_above_below _ _ h },
  { rw fin.succ_above_above _ _ h,
    exact le_of_lt (fin.cast_succ_lt_succ i) }
end

example (x : fin (n + 2)) (y : fin (n + 1)) (j : fin n) :
  x.succ_above (y.succ_above j) = let y' := x.succ_above y in
    let h := fin.succ_above_ne x y in
    x.succ_above ((x.pred_above y' h).succ_above j) :=
begin
  simp only [fin.pred_above_succ_above],
end

example (x y : fin (n + 2)) (j : fin n) (h : y ≠ x) :
  x.succ_above ((x.pred_above y h).succ_above j) = y.succ_above ((y.pred_above x (ne.symm h)).succ_above j) :=
begin
  unfold fin.pred_above,
  split_ifs,
  { exact absurd ‹x < y› (not_lt_of_lt ‹y < x›) },
  { have lessy : y.val < n + 1 := lt_of_lt_of_le ‹y < x› (fin.le_last x),
    have posx : 0 < x.val := lt_of_le_of_lt (fin.zero_le y) ‹y < x›,
    have hx : x ≠ 0 := ne_of_gt posx,
    cases fin.succ_above_lt_ge (y.cast_lt lessy) j with hyj hyj,
    { rw fin.succ_above_below _ _ hyj,
      cases fin.succ_above_lt_ge x j.cast_succ with hxj hxj,
      { rw fin.succ_above_below _ _ hxj,
        have hxj' : j.cast_succ < (x.pred hx),
          { refine lt_trans hyj _,
            rw fin.lt_iff_coe_lt_coe,
            simp,
            exact ‹y < x›,
          },
        rw fin.succ_above_below (x.pred _),
      },
      { sorry },
    },
    { rw fin.succ_above_above _ _ hyj,
      cases fin.succ_above_lt_ge x j.cast_succ with hxj hxj,
      { sorry },
      { sorry },
    },
  },
  { have lessx : x.val < n + 1 := lt_of_lt_of_le ‹x < y› (fin.le_last y),
    cases fin.succ_above_lt_ge (x.cast_lt lessx) j with hxj hxj,
    { rw fin.succ_above_below _ _ hxj,
      cases fin.succ_above_lt_ge x y.cast_succ with hyj hyj,
      { sorry },
      { sorry },
    },
    { rw fin.succ_above_above _ _ hxj,
      cases fin.succ_above_lt_ge x y.cast_succ with hyj hyj,
      { sorry },
      { sorry },
    },
  },
  { cases lt_or_gt_of_ne h,
    { contradiction },
    { contradiction } },
end

#exit

example (x : fin (n + 2)) (y : fin (n + 1)) (j : fin n) :
  x.succ_above (y.succ_above j) = let y' := x.succ_above y in
  dite (y' < x)
    (λ h, y'.succ_above ((y'.pred_above x (ne_of_gt h)).succ_above j))
    (λ h, dite (x < y')
      (λ h', y'.succ_above ((y'.pred_above x (ne_of_lt h')).succ_above j))
      (λ _, 0))
  :=
begin
  simp only [dif_neg (x.succ_above_ne y)],
  set y' := x.succ_above y with hy,
  cases fin.succ_above_lt_ge x y with hyx hyx,
  {
    have posx : 0 < x := lt_of_le_of_lt (fin.zero_le y.cast_succ) hyx,
    have hyx' : y ≤ x.pred (ne_of_gt posx),
      { rw [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ] at hyx,
        rw [fin.le_iff_coe_le_coe, fin.coe_pred],
        exact nat.le_pred_of_lt hyx },
    rw fin.succ_above_below x y hyx at hy,
    rw hy,
    rw dif_pos hyx,
    unfold fin.pred_above,
    rw dif_neg (not_lt_of_lt hyx),
    cases fin.succ_above_lt_ge (x.pred (ne_of_gt posx)) j with hjx hjx,
    { rw fin.succ_above_below (x.pred _) j hjx,
      cases fin.succ_above_lt_ge y j with hjy hjy,
      { rw fin.succ_above_below y j hjy,
        rw fin.succ_above_below y.cast_succ j.cast_succ hjy,
        sorry,
      },
      { rw fin.succ_above_above y j hjy,
        rw fin.succ_above_above y.cast_succ j.cast_succ hjy,
        sorry,
      }
    },
    { rw fin.succ_above_above (x.pred _) j hjx,
      cases fin.succ_above_lt_ge y.cast_succ j.succ with hjy hjy,
      { rw fin.succ_above_below y.cast_succ j.succ hjy,
        have : j.cast_succ < y,
          { rw fin.cast_succ_lt_iff at hjy,
            exact lt_trans (fin.cast_succ_lt_succ _) hjy },
        rw fin.succ_above_below y j this,
        sorry,
      },
      { rw fin.succ_above_above y.cast_succ j.succ hjy,
        have : y ≤ j.cast_succ := le_trans hyx' hjx,
        rw fin.succ_above_above y j this,
        sorry,
      }
    },
  },
  {
    have hyx' : x < y.succ := lt_of_le_of_lt hyx (fin.cast_succ_lt_succ y),
    rw fin.succ_above_above x y hyx at hy,
    rw hy,
    rw dif_neg (not_lt_of_lt hyx'),
    rw dif_pos hyx',
    unfold fin.pred_above,
    rw dif_pos hyx',
    cases fin.succ_above_lt_ge (x.cast_lt (lt_of_lt_of_le hyx' (nat.le_of_lt_succ y.succ.2))) j with hjx hjx,
    { rw fin.succ_above_below (x.cast_lt _) j hjx,
      cases fin.succ_above_lt_ge y j with hjy hjy,
      { rw fin.succ_above_below y j hjy,
        sorry,
      },
      { rw fin.succ_above_above y j hjy,
        sorry,
      }
    },
    { rw fin.succ_above_above (x.cast_lt _) j hjx,
      cases fin.succ_above_lt_ge y j with hjy hjy,
      { rw fin.succ_above_below y j hjy,
        sorry,
      },
      { rw fin.succ_above_above y j hjy,
        sorry,
      }
    },
  },
end

-- example (x : fin (n + 2)) (y : fin (n + 1)) (j : fin n) :
--   x.succ_above (y.succ_above j) = let y' := x.succ_above y in
--   dite (y' = x) (λ _, 0) (λ h, y'.succ_above ((y'.pred_above x (ne.symm h)).succ_above j)) :=
-- begin
--   simp only [dif_neg (x.succ_above_ne y)],
--   set y' := x.succ_above y with hy,
--   have hy' : (y : ℕ) ≤ y' := fin.le_succ_above x y,
--   cases nat.lt_or_ge j y with hjy hjy;
--   cases nat.lt_or_ge j x with hjx hjx;
--   cases nat.lt_or_ge y x with hyx hyx,
--   any_goals
--   { have hy'x : y' ≤ x,
--     { rw [hy, fin.succ_above_below x y hyx],
--       exact le_of_lt hyx },
--     have hyy' : (y : ℕ) = y',
--     { rw [hy, fin.succ_above_below x y hyx, fin.coe_cast_succ] } },
--   any_goals
--   { have hy'x : x < y',
--     { rw [hy, fin.succ_above_above x y hyx, fin.lt_iff_coe_lt_coe],
--       exact lt_of_le_of_lt hyx fin.lt_succ },
--     have hyy' : (y : ℕ) < y',
--       { rw fin.succ_above_above at hy,
--         { rw hy,
--           exact fin.lt_succ },
--         { exact hyx } } },
--   any_goals
--   { have hjy' : (j : ℕ) < y' := lt_of_lt_of_le hjy hy' },
--   any_goals
--   { have hjy' : (y' : ℕ) ≤ j,
--       { rw ←hyy',
--         exact hjy } },
--   any_goals
--   { have hjsy' : (j.succ : ℕ) < y',
--     { rw [fin.coe_succ],
--       exact lt_of_le_of_lt (nat.succ_le_of_lt hjy) hyy' } },
--   any_goals
--   { linarith },
--   { rw fin.succ_above_below y j hjy,
--     rw fin.succ_above_below x j.cast_succ hjx,
--     unfold fin.pred_above,
--     rw dif_neg (not_lt_of_le hy'x),
--     cases nat.lt_or_ge j (x - 1) with H H,
--     { rw fin.succ_above_below _ j,
--       { rw fin.succ_above_below,
--         exact hjy' },
--       { simpa only [fin.lt_iff_coe_lt_coe, fin.coe_pred] using H } },
--     { exact absurd (nat.pred_lt_le (lt_of_le_of_lt H hjy)) (not_le_of_lt hyx) } },
--   { rw fin.succ_above_below y j hjy,
--     rw fin.succ_above_below x j.cast_succ hjx,
--     unfold fin.pred_above,
--     rw dif_pos hy'x,
--     rw fin.succ_above_below _ j,
--       { rw fin.succ_above_below,
--         exact hjy' },
--       { exact hjx } },
--   { rw fin.succ_above_below y j hjy,
--     rw fin.succ_above_above x j.cast_succ hjx,
--     unfold fin.pred_above,
--     rw dif_pos hy'x,
--     rw fin.succ_above_above _ j,
--       { rw [fin.succ_above_below, fin.cast_succ_fin_succ],
--         exact hjsy' },
--       { exact hjx } },
--   { rw fin.succ_above_above y j hjy,
--     rw fin.succ_above_below x,
--     { unfold fin.pred_above,
--       rw dif_neg (not_lt_of_le hy'x),
--       rcases nat.lt_trichotomy y (x - 1) with H|H|H,
--       { rw [fin.succ_above_below _ j],
--         { rw [fin.succ_above_above, fin.cast_succ_fin_succ],
--           exact hjy' },
--         {
--           rcases nat.lt_trichotomy j (x - 1) with H'|H'|H',
--           { simpa only [fin.lt_iff_coe_lt_coe, fin.coe_pred] using H' },
--           {  },
--           {  },
--           },
--         { simpa [fin.lt_iff_coe_lt_coe] using nat.add_lt_of_lt_sub_right H } },
--       { rw [fin.succ_above_below _ j.succ, fin.succ_above_above _ j],
--         { rw [fin.succ_above_above, fin.cast_succ_fin_succ],
--           exact hjy' },
--       },
--       {  } },
--     { exact hjx },
--   },
--   {  },
--   {  },
--   {  },
--   {  },
--   -- simp_rw fin.eq_iff_veq,
--   -- simp_rw ←fin.coe_eq_val,
--   -- unfold fin.succ_above,
--   -- simp_rw fin.lt_iff_coe_lt_coe,
--   -- simp_rw apply_ite coe,
--   -- simp only [fin.coe_succ, fin.coe_cast_succ],
--   -- split_ifs with ha hb hc hd,
--   -- any_goals {simp_rw [fin.coe_cast_succ] at *},
--   -- { exact absurd ha hd },

--   -- simp_rw [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ] at h h_1 h_2,
--   -- split_ifs,
--   -- {
--   --   have H : j.cast_succ < x.pred (ne_of_gt (lt_of_le_of_lt (fin.zero_le y.cast_succ) h_2)),
--   --     { rw fin.lt_iff_coe_lt_coe at *,
--   --       simp at *,
--   --       refine lt_of_lt_of_le h _,
--   --       exact nat.le_pred_of_lt h_2,
--   --     },
--   --   simp [h, h_1, h_2, not_lt_of_lt h, not_lt_of_lt h_1, not_lt_of_lt h_2, H],
--   --   split_ifs,
--   --  },
--   -- {  }
-- end

lemma det_swap_eq_neg_det_dim3 (A : matrix (fin (n + 2)) (fin (n + 2)) R) : det' (swap_row A 0 1) = - det' A :=
begin
  induction n with n hn,
  { exact det_swap_eq_neg_det_dim2 A 1 0 (fin.zero_ne_one.symm) },
  have s1 : ∀ ix : fin (n + 1), A.swap_row 0 1 ix.succ.succ = A ix.succ.succ,
    { intro ix,
      ext col,
      rw swap_row_ne_apply,
      { exact ne_of_gt (fin.succ_pos _) },
      { exact fin.succ_succ_ne_one _ } },
  rw det_laplace_def,
  simp_rw [@det_laplace_def _ _ n],
  simp [minor, fin.succ_above_below, fin.one_pos, s1, mul_add, add_assoc],
  simp_rw [finset.mul_sum],
  symmetry,
  rw [det_laplace_def, ←finset.sum_neg_distrib],
  simp_rw [neg_mul_eq_neg_mul, @det_laplace_def _ _ n],
  simp [minor, fin.succ_above_below, fin.one_pos, s1, mul_add, add_assoc, ←finset.sum_neg_distrib],
  simp_rw [finset.mul_sum, ←finset.sum_neg_distrib, neg_mul_eq_neg_mul],
  have sumswap :
    ∑ x, (∑ y, -A 0 x * (-1) ^ (x : ℕ) * A 1 (x.succ_above y) * (-1) ^ (y : ℕ) * det' (λ (i j : fin (n + 1)), A i.succ.succ (x.succ_above (y.succ_above j)))) =
    ∑ x, (∑ y, A 1 x * (-1) ^ (x : ℕ) * A 0 (x.succ_above y) * (-1) ^ (y : ℕ) * det' (λ (i j : fin (n + 1)), A i.succ.succ (x.succ_above (y.succ_above j)))),
    { ring_exp,
      have lhs : (∑ x : fin (n + 3), ∑ y : fin (n + 2),
          (A 0 x * (A 1 (x.succ_above y) * (det' (λ (i j : fin (n + 1)), A i.succ.succ (x.succ_above (y.succ_above j))) * ((-1) ^ (x : ℕ) * -(-1) ^ (y : ℕ))))))
        = ∑ x : fin (n + 3), ∑ y : fin (n + 3), dite (x = y) (λ _, 0)
                (λ h, (A 0 x * (A 1 y * det' (λ (i j : fin (n + 1)), A i.succ.succ (x.succ_above ((x.pred_above y (ne.symm h)).succ_above j))) * -((-1 : R) ^ (x : ℕ) * (-1) ^ (y : ℕ) * ite (y < x) 1 (-1))))),
        { congr' 1 with x,
          rw [fin.sum_univ_succ_above _ x, dif_pos rfl, zero_add],
          congr' 1 with y,
          rw dif_neg (fin.succ_above_ne x y).symm,
          split_ifs with H H,
          { rw fin.succ_above_lt_iff at H,
            rw [fin.pred_above_succ_above, fin.succ_above_below _ _ H],
            ring_exp },
          { rw fin.succ_above_lt_iff at H,
            rw [fin.pred_above_succ_above, fin.succ_above_above _ _ (le_of_not_lt H), fin.coe_succ],
            ring_exp } },
      have rhs : (∑ x : fin (n + 3), ∑ y : fin (n + 2),
          (A 1 x * (A 0 (x.succ_above y) * (det' (λ (i j : fin (n + 1)), A i.succ.succ (x.succ_above (y.succ_above j))) * ((-1 : R) ^ (x : ℕ) * (-1) ^ (y : ℕ))))))
        = ∑ x : fin (n + 3), ∑ y : fin (n + 3), dite (x = y) (λ _, 0)
                (λ h, (A 1 x * (A 0 y * det' (λ (i j : fin (n + 1)), A i.succ.succ (x.succ_above ((x.pred_above y (ne.symm h)).succ_above j))) * ((-1 : R) ^ (x : ℕ) * (-1) ^ (y : ℕ) * ite (y < x) 1 (-1))))),
        { congr' 1 with x,
          rw [fin.sum_univ_succ_above _ x, dif_pos rfl, zero_add],
          congr' 1 with y,
          rw dif_neg (fin.succ_above_ne x y).symm,
          split_ifs with H H,
          { rw fin.succ_above_lt_iff at H,
            rw [fin.pred_above_succ_above, fin.succ_above_below _ _ H],
            ring_exp },
          { rw fin.succ_above_lt_iff at H,
            rw [fin.pred_above_succ_above, fin.succ_above_above _ _ (le_of_not_lt H), fin.coe_succ],
            ring_exp } },
      rw [lhs, rhs, finset.sum_comm],
      clear lhs rhs,
      congr' 1 with x,
      congr' 1 with y,
      rcases lt_trichotomy x y with h|h|h,
      {
        rw [dif_neg (ne_of_lt h)],
        rw [dif_neg (ne_of_gt h), if_neg (not_lt_of_lt h), if_pos h],
        simp [fin.pred_above_succ_above],
        ring_exp },
      { rw [if_pos h, if_pos h.symm] },
      { rw [if_neg (ne_of_lt h), if_neg (ne_of_gt h), if_neg (not_lt_of_lt h), if_pos h],
        ring_exp } },
  convert sumswap,
end

end det
