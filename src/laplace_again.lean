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
import data.rat.cast

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

lemma det_laplace_def : det' A = ∑ j, (A 0 j * (-1 : R) ^ (j : ℕ) * det' (drop A 0 j)) := rfl

instance fin_inhabited {n : ℕ} : inhabited (fin (n + 1)) := ⟨0⟩

@[simp] lemma fin.default_eq_zero {n : ℕ} : default (fin (n + 1)) = 0 := rfl

@[simp] lemma fin.default_succ_eq_one {n : ℕ} : fin.succ (default (fin (n + 1))) = 1 := rfl

lemma det_swap_eq_neg_det_dim2 (A : matrix (fin 2) (fin 2) R) (i j) (h : i ≠ j) : det' (swap_row A i j) = - det' A :=
begin
  wlog hl : i ≤ j,
  fin_cases i;
  fin_cases j,
  any_goals { contradiction },
  { simp [det_laplace_def, fin.sum_univ_succ, fin.succ_above_below, fin.one_pos, drop_def, minor],
    ring },
  { exact absurd fin.one_pos (not_lt_of_le hl) },
  { rw [←this h.symm, swap_row_symmetric] }
end

lemma det_swap_01_sum_aux (A : matrix (fin (n + 3)) (fin (n + 3)) R) :
  (∑ x, (∑ y, -A 0 x * (-1) ^ (x : ℕ) * A 1 (x.succ_above y) * (-1) ^ (y : ℕ) *
    det' ((A.drop 0 x).drop 0 y))) =
  ∑ x, (∑ y, A 1 x * (-1) ^ (x : ℕ) * A 0 (x.succ_above y) * (-1) ^ (y : ℕ) *
    det' ((A.drop 0 x).drop 0 y)) :=
begin
  rw [fin.sum_collate, fin.sum_collate, finset.sum_comm],
  simp_rw fin.succ_above_descend,
  congr' 1 with x,
  congr' 1 with y,
  rcases lt_trichotomy x y with h|rfl|h,
  { have : 0 < (y : ℕ),
      { exact lt_of_le_of_lt (nat.zero_le _) h },
    rw [dif_neg (ne_of_lt h), dif_neg (ne_of_gt h), drop_drop_comm',
        fin.pred_above, fin.pred_above, dif_pos h, dif_neg (not_lt_of_lt h),
        fin.coe_pred, ring.pow_sub this, fin.coe_cast_lt],
    ring_exp },
  { simp only [dif_pos] },
  { have : 0 < (x : ℕ),
      { exact lt_of_le_of_lt (nat.zero_le _) h },
    rw [dif_neg (ne_of_lt h), dif_neg (ne_of_gt h), drop_drop_comm',
        fin.pred_above, fin.pred_above, dif_pos h, dif_neg (not_lt_of_lt h),
        fin.coe_pred, ring.pow_sub this, fin.coe_cast_lt],
    ring_exp },
end

lemma det_swap01_eq_neg_det (A : matrix (fin (n + 2)) (fin (n + 2)) R) :
  det' (swap_row A 0 1) = - det' A :=
begin
  induction n with n hn,
  { exact det_swap_eq_neg_det_dim2 A 0 1 fin.zero_ne_one },
  have s1 : ∀ ix : fin (n + 1), A.swap_row 0 1 ix.succ.succ = A ix.succ.succ,
    { intro ix,
      ext col,
      rw swap_row_ne_apply,
      { exact ne_of_gt (fin.succ_pos _) },
      { exact fin.succ_succ_ne_one _ } },
  symmetry,
  simp only [det_laplace_def, finset.mul_sum, ←finset.sum_neg_distrib],
  simp_rw [drop_swap_01', drop_drop_01],
  convert det_swap_01_sum_aux A;
  { simp [det_laplace_def, minor, s1, finset.mul_sum, drop_zero_row],
    ring_exp }
end

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
    { rw [←fin.succ_lt_succ_iff, hi, hj],
      simpa only [fin.succ_pred] using h },
  have jpos' : 0 < j' := lt_of_le_of_lt (fin.zero_le i') h',
  rw [det_laplace_def, det_laplace_def],
  simp_rw [←finset.sum_neg_distrib, swap_row_ne_apply _ _ _ _ _
    (ne_of_lt ipos) (ne_of_lt (lt_trans ipos h)),
    drop_swap_zero_comm _ (ne_of_lt h) ipos (lt_trans ipos h)],
  cases eq_or_lt_of_le (fin.zero_le i') with H H,
  { rw [←hi, ←H],
    by_cases Hj : (j' = 1),
    { simp_rw [←hj, Hj, det_swap01_eq_neg_det],
      ring_exp, },
    { replace Hj : 1 < j' := lt_of_le_of_ne jpos' (ne.symm Hj),
      simp_rw [←swap_contract_01 _ Hj, det_swap01_eq_neg_det],
      simp_rw [
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

lemma det''_eq_det'_at_0 (A : matrix (fin (n + 1)) (fin (n + 1)) R) : det'' A 0 = det' A :=
begin
  induction n with n hn,
  { simp only [det', det''] },
  { simp only [det', det'', hn, dif_pos] },
end

lemma det''_eq_det'_dim2 (A : matrix (fin 2) (fin 2) R) (i : fin 2) :
  det'' A i = det' A :=
begin
  rw [det'', det_laplace_def],
  fin_cases i,
  { simp only [det'', dif_pos, fin.val_eq_coe, det_one_eq_elem] },
  { have one_pos : (0 : fin 1).cast_succ < 1 := lt_of_le_of_ne (fin.zero_le 1) fin.zero_ne_one,
    simp [det'', minor, fin.zero_ne_one.symm,
          fin.sum_univ_succ, fin.succ_above_below _ _ one_pos, drop_zero_row],
    ring }
end

lemma drop_swap_det_01 (A : matrix (fin (n + 2)) (fin (n + 2)) R) (jx : fin (n + 2)) :
  det' ((A.swap_row 0 1).drop 0 jx) = det' (A.drop 1 jx) :=
by rw drop_swap_01' A jx

lemma drop_swap_det_0i (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i jx : fin (n + 2))
  (ipos : 0 < i) :
  det' ((A.swap_row 0 i).drop 0 jx) = (-1) ^ ((i : ℕ) + 1) * det' (A.drop i jx) :=
begin
  induction n with n hn,
  { fin_cases i,
    { exact absurd ipos (lt_irrefl 0) },
    { convert drop_swap_det_01 A jx,
      simp only [one_pow, one_mul, fin.coe_one, neg_square] } },
  obtain ⟨i, hi⟩ := i,
  induction i with i IH,
  { exact absurd ipos (lt_irrefl 0) },
  set i' := fin.pred ⟨i.succ, hi⟩ (ne_of_gt ipos) with hi',
  rw fin.pred_succ_iff at hi',
  simp_rw ←hi',
end

lemma drop_swap_det_ij (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i j jx : fin (n + 2))
  (ipos : 0 < i) (h : i < j) :
  det' ((A.swap_row i j).drop i jx) = (-1) ^ ((i : ℕ) + j + 1) * det' (A.drop j jx) :=
begin
  have jpos : 0 < j := lt_trans ipos h,
  induction n with n hn,
  { fin_cases i,
    { exact absurd ipos (lt_irrefl 0) },
    fin_cases j,
    { exact absurd jpos (lt_irrefl 0) },
    { exact absurd h (lt_irrefl 1) } },
  rcases n with _|n,
  { fin_cases i,
    { exact absurd ipos (lt_irrefl 0) },
    { fin_cases j,
      { exact absurd jpos (lt_irrefl 0) },
      { exact absurd h (lt_irrefl 1) },
      { rw [(show (2 : fin 3) = fin.succ 1, by refl), ←fin.cast_succ_one,
            drop_swap_adjacent'],
        simp only [pow_add, mul_one, one_mul, fin.cast_succ_one, fin.coe_one,
                   fin.coe_succ, pow_one, mul_neg_eq_neg_mul_symm, neg_neg]}, },
    { exact absurd h (not_lt_of_le (fin.le_last j)) } },
  set i' := i.pred (ne_of_gt ipos) with hi,
  set j' := j.pred (ne_of_gt jpos) with hj,
  have h' : i' < j',
    { rw [←fin.succ_lt_succ_iff, hi, hj],
      simpa only [fin.succ_pred] using h },
  have jpos' : 0 < j' := lt_of_le_of_lt (fin.zero_le i') h',
  rw [det_laplace_def, det_laplace_def],
  rw [finset.mul_sum],
  congr' 1,
  ext x,
  rw swap_row_ne_apply _ _ _ _ _ (ne_of_lt ipos) (ne_of_lt (lt_trans ipos h)),
  sorry,
  cases eq_or_lt_of_le (fin.zero_le i') with H H,
  { rw fin.pred_succ_iff at hi,
    rw ←hi,
    rw ←H,
    by_cases Hj : (j' = 1),
    { rw fin.pred_succ_iff at hj,
      rw [←hj, Hj, fin.succ_zero_eq_one, ←fin.cast_succ_one],
      rw [drop_swap_adjacent' A],
      simp only [pow_add, mul_one, one_mul, fin.cast_succ_one, fin.coe_one,
                 fin.coe_succ, pow_one, mul_neg_eq_neg_mul_symm, neg_neg] },
    { replace Hj : 1 < j' := lt_of_le_of_ne jpos' (ne.symm Hj),
      simp only [fin.coe_one, fin.val_eq_coe, fin.succ_zero_eq_one],
      rw drop_drop_01,
      ring_exp,
      -- rw drop_swap_zero_comm,
      congr' 1,
      { simp [drop_def, minor, fin.succ_above_below, jpos,
              fin.one_pos, swap_row_ne_apply, fin.zero_ne_one, ne_of_lt jpos] },
      {
        rw ←mul_assoc,
        congr' 1,
        -- rw ←swap_row_thrice _ 1 0 j fin.zero_ne_one.symm (ne_of_lt jpos),
        -- rw swap_row_symmetric,
        have : j.pred_above 0 (ne_of_lt jpos) = 0,
          { simpa only [fin.pred_above, jpos, dif_pos] },
        -- rw ←this,
        rw drop_swap_zero_comm,
        simp,
        rw fin.pred_above_zero,
        simp_rw ←hj,
        specialize hn (A.drop 0 jx) 1 j' x fin.one_pos Hj jpos',
        simp [pow_add] at hn,
        rw ring.pow_sub (fin.lt_iff_coe_lt_coe.mp jpos) at hn,
        ring_exp at hn,
        rw [mul_neg_eq_neg_mul_symm, eq_comm, neg_eq_iff_neg_eq] at hn,
        rw ←hn,
        rw ←det_swap01_eq_neg_det,
        rw drop_swap_01',
        rw drop_drop_01,
        rw ←hj,
        rw drop_drop_0i,
        rw fin.coe_succ,
        rw mul_one,
        rw ←pow_add,
        ring_exp,
        ring_exp at hn,
        rw ←hn,
      },
      rw det_swap_eq_neg_det,
     } },
  {  },
  -- rw fin.pred_succ_iff at hj,
  -- rw ←hj,
  -- { rw fin.mk_zero at ipos,
  --   exact absurd ipos (lt_irrefl 0) },
  -- { set i' : fin (n + 2) := fin.pred ((⟨i.succ, hi⟩ : fin (n + 3))) (ne_of_gt ipos) with hx,
  --   rw fin.pred_succ_iff at hx,
  --   rw ←hx at *,
  --   by_cases H : i' = 0,
  --   { simp only [H, one_pow, one_mul, fin.coe_one, drop_swap_01', fin.succ_zero_eq_one, neg_square], },
  --   },
end

lemma drop_swap_det0j (A : matrix (fin (n + 2)) (fin (n + 2)) R) (j jx : fin (n + 2)) (jpos : 0 < j) :
  det' ((A.swap_row 0 j).drop 0 jx) = (-1) ^ ((j : ℕ) + 1) * det' (A.drop j jx) :=
begin
  induction n with n hn,
  { fin_cases j,
    { exact absurd jpos (lt_irrefl _) },
    { simp only [one_pow, one_mul, fin.coe_one, drop_swap_01', neg_square] } },
  obtain ⟨j, hj⟩ := j,
  induction j with j HJ,
  { simp only [fin.mk_zero] at jpos,
    exact absurd jpos (lt_irrefl _) },
  { set j' : fin (n + 2) := fin.pred ((⟨j.succ, hj⟩ : fin (n + 3))) (ne_of_gt jpos) with hx,
    rw fin.pred_succ_iff at hx,
    rw ←hx,
    by_cases H : j' = 0,
    { simp only [H, one_pow, one_mul, fin.coe_one, drop_swap_01', fin.succ_zero_eq_one, neg_square] },
    {
      have hj' : j < n + 3 := nat.lt_of_succ_lt hj,
      specialize HJ (nat.lt_of_succ_lt hj),
      have : (⟨j, hj'⟩ : fin (n + 3)) = j'.cast_succ := rfl,
      rw this at HJ,
      simp only [nat.succ_sub_succ_eq_sub, fin.coe_cast_succ, fin.coe_pred, nat.sub_zero, fin.coe_mk] at HJ,
      rw [fin.coe_succ, pow_add],
      rw ←drop_swap_adjacent',
      simp,
      rw ←HJ, }
    },
end

lemma drop_swap_det0j' (A : matrix (fin (n + 2)) (fin (n + 2)) R) (j jx : fin (n + 2)) (jpos : 0 < j) :
  det' ((A.swap_row 0 j).drop 0 jx) = (-1) ^ ((j : ℕ) + 1) * det' (A.drop j jx) :=
begin
  revert jpos jx,
  apply elem_matrix.induction_on A j,
  { intros A' j' jpos jx,
    fin_cases j',
    { exact absurd jpos (lt_irrefl _) },
    { simp only [one_pow, one_mul, fin.coe_one, drop_swap_01', neg_square] } },
  { intros jpos jx,
    exact absurd jpos (lt_irrefl _) },
  { intros j' A' IH jpos' jx,
    rw ←swap_row_thrice A' 0 j'.cast_succ,
    rw IH jx,
  },
end

lemma drop_swap_detij (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i j jx : fin (n + 2))
  (h : i < j) (hpos : 0 < i) :
  det' (A.drop j jx) = det' ((A.swap_row i j).drop i jx) :=
begin
  induction n with n hn,
  { fin_cases j,
    { exact absurd h (not_lt_of_le (fin.zero_le i)) },
    { exact absurd h (not_lt_of_le hpos) } },
  {
    have hpos' : 0 < j := lt_trans hpos h,
    by_cases hi : i = 1,
    { rw hi at h ⊢,
      rw ←swap_drop_01',
      rw det_laplace_def,
      rw det_laplace_def,
      congr' 1,
      ext x,
      { simp only [minor, ne_of_lt hpos', fin.zero_ne_one, fin.succ_above_below, hpos', swap_row_ne_apply, fin.cast_succ_zero,
 fin.val_eq_coe, fin.succ_zero_eq_one, ne.def, not_false_iff, swap_row_apply],
        congr' 1,
        { simp [minor, swap_row_ne_apply, ne_of_lt hpos', fin.zero_ne_one, fin.succ_above_below, hpos', drop_def] },
        {
          simp_rw [←drop_01],
          simp_rw [swap_drop_01],
          -- simp_rw [←drop_01],
          rw [swap_drop_zero_comm _ (ne_of_lt h) fin.one_pos hpos'],
          simp [drop_zero_row, minor, drop_def],
          },
        ext y z,
                },
      rcases eq_or_lt_of_le (fin.zero_le x) with rfl|H,
      { simp [minor, ne_of_lt hpos', fin.zero_ne_one, fin.succ_above_below, hpos'] },
      { have : 1 ≤ x := H,
        rcases eq_or_lt_of_le this with rfl|H',
        {
          have s1 : fin.succ (1 : fin (n + 2)) ≠ 1,
          { intro h,
            rw fin.eq_iff_veq at h,
            exact (nat.succ_ne_self 1) h },
          have s0 : fin.succ (1 : fin (n + 2)) ≠ 0 := ne_of_gt (fin.succ_pos 1),
          cases fin.succ_above_lt_ge j 1 with H' H',
          simp [minor, ne_of_lt hpos', fin.zero_ne_one, fin.succ_above_below, hpos',
                swap_row_ne_apply, s0, s1, H'],
          },
        simp [minor, ne_of_lt hpos', fin.zero_ne_one, fin.succ_above_below, hpos'], },

    },
    simp_rw [det_laplace_def],
    congr,
    ext x,
    have hswap : A.swap_row i j 0 = A 0,
      { ext jx,
        rw swap_row_ne_apply _ _ _ _ _ (ne_of_lt hpos) (ne_of_lt hpos') },
    simp only [minor, fin.succ_above_below, hpos, hpos', hswap, fin.cast_succ_zero, fin.val_eq_coe],
    congr' 1,
    { simp [minor, fin.succ_above_below, hpos, hpos', hswap] },
    have drop_drop : ∀ (A : matrix (fin (n + 3)) (fin (n + 3)) R),
      ∀ row, ∀ (h : row ≠ 0), (A.drop row jx).drop 0 x = (A.drop 0 jx).drop (row.pred h) x,
      { intros A j h,
        ext ix jx,
        have : j.succ_above ix.succ = ((j.pred h).succ_above ix).succ,
          { cases fin.succ_above_lt_ge (j.pred h) ix with H H,
            { rw [fin.succ_above_below, fin.succ_above_below, fin.cast_succ_fin_succ],
              { exact H },
              { rw ←fin.succ_lt_succ_iff at H,
                simpa only [fin.cast_succ_fin_succ, fin.succ_pred] using H } },
            { rw [fin.succ_above_above, fin.succ_above_above],
              { exact H },
              { rw ←fin.succ_le_succ_iff at H,
                simpa only [fin.cast_succ_fin_succ, fin.succ_pred] using H } } },
        simp [minor, this] },
    rw drop_drop _ j (ne_of_gt hpos'),
    rw hn _ (i.pred (ne_of_gt hpos)),
    rw drop_drop _ i (ne_of_gt hpos),
    congr,
    cases fin.succ_above_lt_ge j y.succ with H H,
    { rw fin.succ_above_below _ _ H,
    },
    {  },
  }
end

lemma drop_swap_det' (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i j) :
  det' (A.drop i j) = det' ((A.swap_row 0 i).drop 0 j) :=
begin
  induction n with n hn,
  { fin_cases i;
    simp [minor, fin.succ_above_below, fin.one_pos] },
  {
    rcases eq_or_lt_of_le (fin.zero_le i) with rfl|hi,
    { simp },
    {

    },
  },
end

lemma det''_eq_det'_dim3 (A : matrix (fin (n + 2)) (fin (n + 2)) R) (i : fin (n + 2)) :
  det'' A i = det' A :=
begin
  induction n with n hn,
  { exact det''_eq_det'_dim2 A i },
  {rcases eq_or_lt_of_le (fin.zero_le i) with rfl|hi,
    { simp only [det'', det', hn, dif_pos] },
    { rw [det'', dif_neg (ne_of_gt hi)],
      simp_rw [hn],
      rw fin.sum_univ_succ_above _ i,
      rw ←neg_inj,
      rw neg_add,
      rw neg_mul_eq_mul_neg,
      rw ←finset.sum_neg_distrib,
      symmetry,
      ring_exp,
      rw ←det_swap_eq_neg_det A 0 i (ne_of_lt hi),
      rw ←neg_inj,
      rw ←det_swap_eq_neg_det _ 0 i (ne_of_lt hi),
      rw det',
      rw fin.sum_univ_succ_above _ i,
      rw mul_assoc,
      -- rw ←hn _ (i.pred (ne_of_gt hi)),
      rw swap_row_swap_apply,
      congr' 2,
      {
        rw det',
        rw det',
        by_cases hi' : i = 1,
        { have hip : i.pred (ne_of_gt hi) = 0 := hi'.symm ▸ fin.pred_one,
          have hle : ∀ (i : fin (n + 1)), 1 ≤ i.succ,
            { intro i,
              rcases eq_or_lt_of_le (fin.zero_le i) with rfl|H,
              { rw fin.succ_zero_eq_one },
              { rw ←fin.succ_lt_succ_iff at H,
                exact le_of_lt H } },
          have hswap : ∀ (i : fin (n + 1)) jx, A.swap_row 0 1 i.succ.succ jx = A i.succ.succ jx,
            { intros ix jx,
              rw swap_row_ne_apply,
              { exact (ne_of_gt (fin.succ_pos ix.succ)) },
              { exact (ne_of_gt (fin.one_lt_succ_succ ix)) } },
          have habove : ∀ (ix : fin (n + 1)), fin.succ_above 1 ix.succ = ix.succ.succ,
            { intros ix,
              rw fin.succ_above_above,
              rw fin.le_iff_coe_le_coe,
              exact hle ix },
          simp [det_laplace_def, hip, hi', minor, hswap, habove, hle,
                fin.succ_above_below, fin.one_pos] },
        { have hi'' : 1 < i := lt_of_le_of_ne hi (ne.symm hi'),
          have hip : 0 ≠ i.pred (ne_of_gt hi),
            { intro H,
              rw fin.pred_succ_iff at H,
              rw [←H, fin.succ_zero_eq_one] at hi'',
              exact absurd hi'' (lt_irrefl 1) },
          have hswap : ∀ (i : fin (n + 1)) jx, A.swap_row 0 1 i.succ.succ jx = A i.succ.succ jx,
            { intros ix jx,
              rw swap_row_ne_apply,
              { exact (ne_of_gt (fin.succ_pos ix.succ)) },
              { exact (ne_of_gt (fin.one_lt_succ_succ ix)) } },
          have hswap' : ∀ jx, A.swap_row 0 i 1 jx = A 1 jx,
            { intros jx,
              rw swap_row_ne_apply,
              { exact fin.zero_ne_one.symm },
              { exact (ne.symm hi') } },
          have habove : i.succ_above 0 = 0,
            { rw fin.succ_above_below,
              { exact fin.cast_succ_zero },
              { rw fin.lt_iff_coe_lt_coe,
                exact hi } },
          simp [hip.symm, minor, hswap, hswap', habove],
          ring_exp,
          congr,
          ext x,
        },
      },
      -- { rw det'',
      --   by_cases hi' : i = 1,
      --   { have hip : i.pred (ne_of_gt hi) = 0 := hi'.symm ▸ fin.pred_one,
      --     have hle : ∀ (i : fin (n + 1)), 1 ≤ i.succ,
      --       { intro i,
      --         rcases eq_or_lt_of_le (fin.zero_le i) with rfl|H,
      --         { rw fin.succ_zero_eq_one },
      --         { rw ←fin.succ_lt_succ_iff at H,
      --           exact le_of_lt H } },
      --     have hswap : ∀ (i : fin (n + 1)) jx, A.swap_row 0 1 i.succ.succ jx = A i.succ.succ jx,
      --       { intros ix jx,
      --         rw swap_row_ne_apply,
      --         { exact (ne_of_gt (fin.succ_pos ix.succ)) },
      --         { exact (ne_of_gt (fin.one_lt_succ_succ ix)) } },
      --     have habove : ∀ (ix : fin (n + 1)), fin.succ_above 1 ix.succ = ix.succ.succ,
      --       { intros ix,
      --         rw fin.succ_above_above,
      --         rw fin.le_iff_coe_le_coe,
      --         exact hle ix },
      --     simp [det_laplace_def, hip, hi', minor, hswap, habove, hle,
      --           det''_eq_det'_at_0, fin.succ_above_below, fin.one_pos] },
      --   {
      --     have hi'' : 1 < i := lt_of_le_of_ne hi (ne.symm hi'),
      --     have hip : 0 ≠ i.pred (ne_of_gt hi),
      --       { intro H,
      --         rw fin.pred_succ_iff at H,
      --         rw [←H, fin.succ_zero_eq_one] at hi'',
      --         exact absurd hi'' (lt_irrefl 1) },
      --     have hle : ∀ (i : fin (n + 1)), 1 ≤ i.succ,
      --       { intro i,
      --         rcases eq_or_lt_of_le (fin.zero_le i) with rfl|H,
      --         { rw fin.succ_zero_eq_one },
      --         { rw ←fin.succ_lt_succ_iff at H,
      --           exact le_of_lt H } },
      --     have hswap : ∀ (i : fin (n + 1)) jx, A.swap_row 0 1 i.succ.succ jx = A i.succ.succ jx,
      --       { intros ix jx,
      --         rw swap_row_ne_apply,
      --         { exact (ne_of_gt (fin.succ_pos ix.succ)) },
      --         { exact (ne_of_gt (fin.one_lt_succ_succ ix)) } },
      --     have habove : ∀ (ix : fin (n + 1)), fin.succ_above 1 ix.succ = ix.succ.succ,
      --       { intros ix,
      --         rw fin.succ_above_above,
      --         rw fin.le_iff_coe_le_coe,
      --         exact hle ix },
      --     simp [hip.symm, det_laplace_def, minor, fin.succ_above_below, hi],
      --     ring_exp,
      --     congr,
      --     ext x,
      --     congr' 1,
      --   },
    }
  }
end

lemma det''_eq_det' (A : matrix (fin n) (fin n) R) (i : fin n) :
  det'' A i = det' A :=
begin
  rcases n with _|n,
  { exact fin_zero_elim i },
  induction n with n hn,
  { rw [det'', det', subsingleton.elim i 0] },
  { rcases eq_or_lt_of_le (fin.zero_le i) with rfl|hi,
    { simp only [det'', det', hn, dif_pos] },
    { cases n,
      rw [det'', dif_neg (ne_of_gt hi)],
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
      rw swap_row_swap_apply,
      rw det_laplace_def,
      -- congr' 2,
      -- {
      --   -- have drop_swap_comm :
      --   --   (A.swap_row 0 i).drop 0 i = (A.drop i i),
      --   --   { ext x y,
      --   --     by_cases hx : x = 0;
      --   --     by_cases hxi : x = i.pred (ne_of_gt hi),
      --   --     { rw [hx, fin.pred_succ_iff] at hxi,
      --   --       simp_rw [hx, drop_zero_row, minor, drop_def,
      --   --                hxi, swap_row_apply, minor, ←hxi,
      --   --                fin.succ_above_below _ 0 (fin.cast_succ_lt_succ 0),
      --   --                fin.cast_succ_zero] },
      --   --     { rw [hx, fin.pred_succ_iff] at hxi,
      --   --       simp_rw [hx, drop_zero_row, minor, drop_def, minor],
      --   --       rw [swap_row_ne_apply],
      --   --       { sorry },
      --   --       { exact (ne_of_gt (fin.succ_pos 0)) },
      --   --       { exact hxi },
      --   --     },
      --   --     {  },
      --   --     {  },
      --   --     -- { simp [hxi, minor], },
      --   --     -- by_cases hxj : x = j',
      --   --     -- { simp [hxj, minor] },
      --   --     -- { rw swap_row_ne_apply _ _ _ _ _ hxi hxj,
      --   --     --   rw fin.pred_succ_iff at hxi hxj,
      --   --     --   simp only [minor, drop_zero_row, swap_row_ne_apply,
      --   --     --               hxi, hxj, ne.def, not_false_iff] }
      --   --                   },
      --    simp, },
      -- { sorry },
    },
  },
end


end det
