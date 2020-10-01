import data.fin
import tactic.norm_num
import tactic.linarith
import data.fintype.card
import algebra.group_with_zero_power

open_locale big_operators

lemma nat.not_lt_pred_ge {m n : ℕ} (h : m < n - 1) (H : n ≤ m) : false :=
begin
  have hn : n < n - 1 := lt_of_le_of_lt H h,
  cases n,
  { rw [nat.nat_zero_eq_zero, nat.zero_sub] at hn,
    exact absurd hn (lt_irrefl 0) },
  { rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at hn,
    exact nat.not_succ_lt_self hn },
end

lemma nat.sub_add_one {n : ℕ} (hpos : 0 < n) : n - 1 + 1 = n :=
begin
  cases n,
  { exact absurd hpos (lt_irrefl 0) },
  simp only [nat.succ_sub_succ_eq_sub, nat.sub_zero],
end

lemma nat.lt_one {n : ℕ} (h : n < 1) : n = 0 :=
begin
  cases n,
  { refl },
  { exact absurd (nat.lt_of_succ_lt_succ h) (not_lt_of_le (nat.zero_le n)) }
end

lemma fin.lt_succ_iff_le_cast_succ {n : ℕ} {x : fin n} {y : fin (n + 1)} :
  y < x.succ ↔ y ≤ x.cast_succ :=
begin
  rw [fin.lt_iff_coe_lt_coe, fin.le_iff_coe_le_coe, fin.coe_succ, fin.coe_cast_succ],
  exact nat.lt_add_one_iff,
end

lemma fin.succ_le_iff_cast_succ_lt {n : ℕ} {x : fin n} {y : fin (n + 1)} :
  x.succ ≤ y ↔ x.cast_succ < y :=
begin
  rw [fin.lt_iff_coe_lt_coe, fin.le_iff_coe_le_coe, fin.coe_succ, fin.coe_cast_succ],
  exact iff.rfl
end

@[simp] lemma fin.cast_succ_one {n : ℕ} : fin.cast_succ (1 : fin (n + 2)) = 1 := rfl

@[simp] lemma fin.cast_succ_le_cast_succ_iff {n : ℕ} {a b : fin n} : a.cast_succ ≤ b.cast_succ ↔ a ≤ b :=
by { simp only [fin.le_iff_coe_le_coe, fin.coe_cast_succ] }

@[simp] lemma fin.cast_succ_lt_cast_succ_iff {n : ℕ} {a b : fin n} : a.cast_succ < b.cast_succ ↔ a < b :=
by { simp only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ] }

lemma fin.lt_one_eq_zero {n : ℕ} {x : fin (n + 1)} (h : x < 1) : x = 0 :=
begin
  rcases eq_or_lt_of_le (fin.zero_le x) with rfl|H,
  { refl },
  { cases n,
    { simp only [eq_iff_true_of_subsingleton] },
    { refine absurd (lt_of_le_of_lt _ h) (lt_irrefl _),
      exact H } }
end

lemma ring.pow_pred {R : Type*} [ring R] {x : ℕ} (hpos : 0 < x) :
  (-1 : R) ^ (x.pred) = - (-1) ^ x :=
begin
  cases x,
  { exact absurd hpos (lt_irrefl _) },
  simp [pow_succ]
end

lemma ring.pow_sub {R : Type*} [ring R] {x : ℕ} (hpos : 0 < x) :
  (-1 : R) ^ (x - 1) = - (-1) ^ x :=
begin
  cases x,
  { exact absurd hpos (lt_irrefl _) },
  simp [pow_succ]
end

lemma fin.pred_succ_iff {n : ℕ} (x : fin (n + 1)) (y : fin n) (hx : x ≠ 0) :
  y = x.pred hx ↔ y.succ = x :=
⟨λ h, h.symm ▸ (fin.succ_pred x hx), λ h, by simp_rw [←h, fin.pred_succ] ⟩

lemma fin.succ_above_succ_above_swap {n : ℕ} (x y : fin (n + 2)) (h : y ≠ x) (j : fin n) :
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

lemma fin.sum_collate {R : Type*} [semiring R] {n : ℕ} (f : fin (n + 1) → fin n → R) :
  (∑ (x : fin (n + 1)), ∑ (y : fin n), f x y) =
  ∑ x y, dite (y = x) (λ _, 0) (λ h, f x (x.pred_above y h)) :=
begin
  congr' 1,
  ext x,
  rw [fin.sum_univ_succ_above _ x, dif_pos rfl, zero_add],
  congr' 1 with y,
  rw [dif_neg (fin.succ_above_ne x y), fin.pred_above_succ_above]
end

@[simp] lemma fin.pred_above_zero {n : ℕ} (i : fin (n + 1)) :
  fin.pred_above 0 i = i.pred :=
by { funext, simp only [fin.pred_above, not_lt_of_le i.zero_le, dif_neg, not_false_iff] }

example {R : Type} [ring R] {x y : R} (h : x = -y) : -x = y :=
by { rw neg_eq_iff_neg_eq,  }

-- lemma nat.not_le_pred_gt {m n : ℕ} (h : m ≤ n - 1) (H : n < m) : false :=
-- begin
--   have hn : n < n - 1 := lt_of_lt_of_le H h,
--   cases n,
--   { rw [nat.nat_zero_eq_zero, nat.zero_sub] at hn,
--     exact absurd hn (lt_irrefl 0) },
--   { rw [nat.succ_sub_succ_eq_sub, nat.sub_zero] at hn,
--     exact nat.not_succ_lt_self hn },
-- end

-- lemma nat.le_pred_eq_succ_le {m n : ℕ} (hpos : 0 < m) (h : n ≤ m - 1) : n + 1 ≤ m :=
-- begin
--   cases m,
--   { exfalso, exact nat.lt_asymm hpos hpos },
--   { exact nat.lt_succ_iff.mpr h }
-- end

-- lemma nat.le_pred_eq_succ_le' {m n : ℕ} (h : n - 1 ≤ m) : n ≤ m + 1 :=
-- begin
--   cases m,
--   { exact nat.le_add_of_sub_le_right h },
--   { exact nat.le_add_of_sub_le_right h }
-- end

-- lemma fin.cast_succ_lt_iff (x y : fin n) : x.cast_succ < y.cast_succ ↔ x < y :=
-- begin
--   rw [fin.lt_iff_coe_lt_coe, fin.lt_iff_coe_lt_coe],
--   exact iff.rfl
-- end

-- lemma fin.cast_succ_le_iff (x y : fin n) : x.cast_succ ≤ y.cast_succ ↔ x ≤ y :=
-- begin
--   rw [fin.le_iff_coe_le_coe, fin.le_iff_coe_le_coe],
--   exact iff.rfl
-- end

-- lemma fin.le_succ_above (p : fin (n + 1)) (i : fin n) : i.cast_succ ≤ p.succ_above i :=
-- begin
--   cases fin.succ_above_lt_ge p i,
--   { rw fin.succ_above_below _ _ h },
--   { rw fin.succ_above_above _ _ h,
--     exact le_of_lt (fin.cast_succ_lt_succ i) }
-- end
-- instance fin_lattice {n : ℕ} : bounded_distrib_lattice (fin (n + 1)) := {
--   top := fin.last n,
--   le_top := fin.le_last,
--   bot := 0,
--   bot_le := fin.zero_le,
--   ..distrib_lattice_of_decidable_linear_order
--   }

-- instance lattice_fins {n : ℕ} : lattice (Π n, fin (n + 1)) := @pi.lattice _ _ _

-- variables (m n : ℕ)
-- #check ((⊥ : (Π n, fin (n + 1))) 2)

-- @[simp] lemma nat.pred_succ_ne_zero (n : ℕ) (h : n ≠ 0) : n.pred.succ = n :=
-- by { cases n, exact absurd rfl h, rw nat.pred_succ }

-- section bit

-- -- lemma bit0_lt {k n : ℕ} (h : bit0 k < n) : k < n :=
-- -- by { rw bit0 at h, exact lt_of_le_of_lt (nat.le_add_right _ _) h }

-- -- lemma bit1_lt {k n : ℕ} (h : bit1 k < n) : k < n :=
-- -- by { rw [bit1, bit0, add_assoc] at h, exact lt_of_le_of_lt (nat.le_add_right _ _) h }

-- end bit

-- section fin

-- lemma ne_iff_vne {n : ℕ} (a b : fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
-- ⟨fin.vne_of_ne, fin.ne_of_vne⟩

-- section bit

-- -- @[simp] lemma fin.bit0_val {n : ℕ} : ∀ k : fin n, (bit0 k).val = bit0 (k.val) % n
-- -- | ⟨_, _⟩ := rfl

-- -- @[simp] lemma fin.bit1_val {n : ℕ} (k : fin (n + 1)) : (bit1 k).val = (bit1 (k.val)) % (n + 1) :=
-- -- by simp [bit1, bit0, fin.add_def, fin.one_val]

-- -- @[simp] lemma fin.mk_bit0 {n : ℕ} (k : ℕ) (h : bit0 k < n) : (bit0 ⟨k, bit0_lt h⟩ : fin n) = ⟨bit0 k, h⟩ :=
-- -- by rw [fin.eq_iff_veq, fin.bit0_val, nat.mod_eq_of_lt h]

-- -- @[simp] lemma fin.mk_bit1 {n : ℕ} (k : ℕ) (h : bit1 k < n + 1) : (bit1 ⟨k, bit1_lt h⟩ : fin (n + 1)) = ⟨bit1 k, h⟩ :=
-- -- by rw [fin.eq_iff_veq, fin.bit1_val, nat.mod_eq_of_lt h]

-- end bit

-- lemma fin.eq_mk_iff_val_eq {n : ℕ} {a : fin n} {b : ℕ} {hb : b < n} : a = ⟨b, hb⟩ ↔ a.val = b :=
-- fin.eq_iff_veq a ⟨b, hb⟩

-- @[simp] lemma fin.mk_zero_eq_zero {n : ℕ} : (⟨0, nat.succ_pos'⟩ : fin (n + 1)) = 0 := rfl

-- @[simp] lemma fin.mk_one_eq_one {n : ℕ} : (⟨1, nat.succ_lt_succ (nat.succ_pos n)⟩ : fin (n + 2)) = 1 := rfl

-- section last

-- @[simp] lemma fin.coe_nat_eq_last (n : ℕ) : (n : fin (n + 1)) = fin.last n :=
-- by { rw [<-fin.of_nat_eq_coe, fin.of_nat, fin.last], simp only [nat.mod_eq_of_lt n.lt_succ_self] }

-- lemma fin.le_coe_last {n : ℕ} (i : fin (n + 1)) : i ≤ n :=
-- by { rw fin.coe_nat_eq_last, exact fin.le_last i }

-- lemma zero_lt_last {n : ℕ} : (0 : fin (n + 2)) < fin.last (n + 1) := by simp [fin.lt_iff_val_lt_val]

-- lemma fin.zero_ne_not_last_add_one {n : ℕ} (i : fin (n + 1)) (hl : i < fin.last n) : (0 : fin (n + 1)) ≠ i + 1 :=
-- begin
--   intro h,
--   rw [fin.lt_iff_val_lt_val, fin.last_val] at hl,
--   cases n,
--   { exact nat.not_lt_zero i.val hl },
--   { rw <-add_lt_add_iff_right 1 at hl,
--     rw [fin.eq_iff_veq, fin.add_def, fin.zero_val, fin.val_one, nat.mod_eq_of_lt hl] at h,
--     exact nat.succ_ne_zero _ h.symm }
-- end

-- lemma fin.zero_ne_one {n : ℕ} : (0 : fin (n + 2)) ≠ 1 :=
-- fin.zero_ne_not_last_add_one 0 zero_lt_last

-- end last

-- section succ

-- lemma fin.succ_pos {n : ℕ} (a : fin n) : (0 : fin (n + 1)) < a.succ := by simp [fin.lt_iff_val_lt_val]

-- lemma cast_succ_ne_succ {n: ℕ} (i : fin (n + 1)) : i.cast_succ ≠ i.succ :=
-- begin
--   intro h,
--   rw [fin.cast_succ, fin.eq_iff_veq, fin.cast_add_val, fin.succ_val] at h,
--   exact (nat.succ_ne_self _) h.symm
-- end

-- lemma cast_succ_lt_succ {n : ℕ} (i : fin (n + 1)) : i.cast_succ < i.succ :=
-- by { rw [fin.lt_iff_val_lt_val, fin.cast_succ, fin.cast_add_val, fin.succ_val], exact lt_add_one _ }

-- @[simp] lemma succ_above_below {n : ℕ} (p : fin (n + 1)) (i : fin n) (h : i.val < p.val) : p.succ_above i = i.cast_succ :=
-- by { rw [fin.succ_above], split_ifs, refl }

-- @[simp] lemma succ_above_above {n : ℕ} (p : fin (n + 1)) (i : fin n) (h : p.val ≤ i.val) : p.succ_above i = i.succ :=
-- by { rw [fin.succ_above], split_ifs with H, { exfalso, exact nat.lt_le_antisymm H h }, refl }

-- @[simp] lemma succ_above_zero {n : ℕ} : fin.succ_above (0 : fin (n + 1)) = fin.succ := rfl

-- @[simp] lemma succ_above_last {n : ℕ} : fin.succ_above (fin.last n) = fin.cast_succ :=
-- by {ext i, simp only [fin.succ_above, i.is_lt, if_true, fin.last_val] }

-- lemma succ_above_pos {n : ℕ} (p : fin (n + 2)) (i : fin (n + 1)) (h : 0 < i) : 0 < p.succ_above i :=
-- begin
--   by_cases H : i.val < p.val,
--   { simpa [succ_above_below, H, fin.lt_iff_val_lt_val] using h },
--   { push_neg at H,
--     simp [succ_above_above, H, fin.lt_iff_val_lt_val], },
-- end

-- lemma succ_above_inj_about_pivot {n : ℕ} {x : fin (n + 1)} {a b : fin n} :
--   x.succ_above a = x.succ_above b ↔ a = b :=
-- begin
--   unfold fin.succ_above,
--   refine iff.intro _ (λ h, by rw h),
--   intro h,
--   split_ifs at h with ha hb hb ha,
--   { exact fin.cast_succ_inj.mp h },
--   { simp [fin.eq_iff_veq] at h,
--     rw h at ha,
--     exact absurd (nat.lt_of_succ_lt ha) hb },
--   { simp [fin.eq_iff_veq] at h,
--     rw ←h at hb,
--     exact absurd (nat.lt_of_succ_lt hb) ha },
--   { exact fin.succ.inj h }
-- end

-- @[simp] lemma cast_succ_zero {n : ℕ} : fin.cast_succ (0 : fin (n + 1)) = 0 := rfl

-- @[simp] lemma fin.succ_zero_eq_one {n : ℕ} : fin.succ (0 : fin (n + 1)) = 1 := rfl

-- lemma fin.succ_succ_ne_one {n : ℕ} (i : fin n) : fin.succ (fin.succ i) ≠ 1 :=
-- by { intro h, rw [<-fin.succ_zero_eq_one, fin.succ_inj] at h, exact (fin.succ_ne_zero i) h }

-- @[simp] lemma fin.coe_eq_cast_succ {n : ℕ} (i : fin n) : (i : fin (n + 1)) = i.cast_succ :=
-- begin
--   rw [fin.cast_succ, fin.cast_add, fin.cast_le, fin.cast_lt, fin.eq_iff_veq],
--   apply fin.coe_val_of_lt,
--   exact nat.lt.step i.is_lt,
-- end

-- @[simp] lemma fin.coe_succ_eq_succ {n : ℕ} (i : fin n) : (i.cast_succ + 1) = i.succ :=
-- begin
--   cases n,
--   { exact fin.elim0 i },
--   { simp [i.is_lt, fin.eq_iff_veq, fin.add_def, nat.mod_eq_of_lt] }
-- end

-- lemma fin.lt_succ {n : ℕ} (i : fin n) : i.cast_succ < i.succ :=
-- begin
--   rw [fin.cast_succ, fin.lt_iff_val_lt_val, fin.cast_add_val, fin.succ_val],
--   exact lt_add_one i.val
-- end

-- lemma fin.lt_succ' {n : ℕ} (i : fin n) : (i : fin (n + 1)) < (i + 1) :=
-- by simp [fin.lt_succ _]

-- end succ

-- section pred

-- @[simp] lemma pred_one {n : ℕ} : fin.pred (1 : fin (n + 2)) (fin.zero_ne_one.symm) = 0 := rfl

-- end pred

-- end fin
