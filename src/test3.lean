import data.matrix.notation
import tactic.wlog
import tactic.omega
import tactic.linarith

variables {n : ℕ}

lemma nat.sub_add_one (hpos : 0 < n) : n - 1 + 1 = n :=
begin
  cases n,
  { exact absurd hpos (lt_irrefl 0) },
  simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
end

lemma nat.not_lt_pred_ge {m n : ℕ} (h : m < n - 1) (H : n ≤ m) : false :=
begin
  have hn : n < n - 1 := lt_of_le_of_lt H h,
  cases n,
  { rw [nat.nat_zero_eq_zero, nat.zero_sub] at hn,
    exact absurd hn (lt_irrefl 0) },
  { rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at hn,
    exact nat.not_succ_lt_self hn },
end


example (x y : fin (n + 2)) (j : fin n) (h : y ≠ x) :
  x.succ_above ((x.pred_above y h).succ_above j) = y.succ_above ((y.pred_above x (ne.symm h)).succ_above j) :=
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

example (x y : fin (n + 2)) (j : fin n) (h : y ≠ x) :
  x.succ_above ((x.pred_above y h).succ_above j) = y.succ_above ((y.pred_above x (ne.symm h)).succ_above j) :=
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

example (x y : fin (n + 2)) (j : fin n) (h : y ≠ x) :
  x.succ_above ((x.pred_above y h).succ_above j) = y.succ_above ((y.pred_above x (ne.symm h)).succ_above j) :=
begin
  wlog H : y < x using [x y],
  { rcases lt_trichotomy x y with H|rfl|H,
    { exact or.inr H },
    { contradiction },
    { exact or.inl H } },
  unfold fin.pred_above,
  rw [dif_pos H, dif_neg (not_lt_of_lt H)],
  have lessy : y.val < n + 1 := lt_of_lt_of_le ‹y < x› (fin.le_last x),
  have posx : 0 < x.val := lt_of_le_of_lt (fin.zero_le y) ‹y < x›,
  have hx : x ≠ 0 := ne_of_gt posx,
  cases fin.succ_above_lt_ge y j.succ with Hyj Hyj,
  { have hyj : j.cast_succ < y.cast_lt lessy,
      { rw fin.lt_iff_coe_lt_coe at Hyj ⊢,
        refine lt_trans _ Hyj,
        simp only [nat.succ_pos', lt_add_iff_pos_right,
                    fin.coe_succ, fin.coe_cast_succ] },
    rw fin.succ_above_below _ _ hyj,
    cases fin.succ_above_lt_ge (x.pred hx) j with hxj hxj,
    { rw fin.succ_above_below _ _ hxj,
      rw fin.succ_above_below,
      rw fin.succ_above_below,
      { exact hyj },
      { rw fin.lt_iff_coe_lt_coe,
        refine lt_trans hxj _,
        rw [fin.val_eq_coe, fin.coe_pred],
        exact nat.pred_lt (ne_of_gt posx) } },
    { cases eq_or_lt_of_le hxj with Hxj Hxj,
      { rw [fin.cast_succ_fin_succ, ←Hxj, fin.succ_pred] at Hyj,
        exact absurd H (not_lt_of_lt Hyj) },
      { rw fin.succ_above_above _ _ hxj,
        rw fin.succ_above_above x,
        rw fin.succ_above_below y _ Hyj,
        { rw fin.cast_succ_fin_succ },
        { rw fin.le_iff_coe_le_coe,
          rw [fin.coe_cast_succ],
          refine nat.le_of_pred_lt _,
          convert Hxj,
          simpa only [fin.val_eq_coe, fin.coe_pred] } } } },
  { rcases eq_or_lt_of_le Hyj with hyj|hyj,
    { simp_rw [hyj, fin.cast_lt_cast_succ],
      rw fin.succ_above_below _ _ (fin.cast_succ_lt_succ j),
      rw fin.succ_above_below x,
      rw fin.succ_above_below (x.pred hx),
      rw fin.cast_succ_fin_succ,
      rw fin.succ_above_below _ _ (fin.cast_succ_lt_succ j.cast_succ),
      { rw fin.lt_iff_coe_lt_coe,
        rw [fin.coe_cast_succ, fin.coe_pred],
        refine nat.le_pred_of_lt _,
        convert H,
        simp only [hyj, fin.val_eq_coe, fin.coe_succ, fin.coe_cast_succ] },
      { refine lt_trans _ H,
        rw [hyj, fin.cast_succ_fin_succ],
        exact fin.cast_succ_lt_succ _ } },
    { replace Hyj : y ≤ j.cast_succ.cast_succ,
        { rw fin.lt_iff_coe_lt_coe at hyj,
          rw [fin.coe_cast_succ, fin.coe_succ] at hyj,
          exact nat.lt_succ_iff.mp hyj },
      have hyj' : y.cast_lt lessy ≤ j.cast_succ,
        { rw fin.le_iff_coe_le_coe at Hyj ⊢,
          refine le_trans Hyj _,
          rw fin.coe_cast_succ },
        rw fin.succ_above_above _ _ hyj',
      cases fin.succ_above_lt_ge (x.pred hx) j with hxj hxj,
      { rw fin.succ_above_below _ _ hxj,
        rw fin.succ_above_above y _,
        rw fin.succ_above_below,
        { rw fin.cast_succ_fin_succ },
        { rw fin.lt_iff_coe_lt_coe,
          rw [fin.coe_cast_succ, fin.coe_succ],
          refine nat.add_lt_of_lt_sub_right _,
          convert hxj,
          rw [fin.val_eq_coe, fin.coe_pred] },
        { rw fin.le_iff_coe_le_coe,
          exact hyj' } },
      { rw fin.succ_above_above _ _ hxj,
        rw fin.succ_above_above x,
        rw fin.succ_above_above y _ (le_of_lt hyj),
        rw [fin.le_iff_coe_le_coe, fin.coe_cast_succ, fin.coe_succ],
        refine nat.le_add_of_sub_le_right _,
        convert hxj,
        rw [fin.val_eq_coe, fin.coe_pred] } } }
end
