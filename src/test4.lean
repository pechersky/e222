import tactic.linarith
import tactic.fin_cases
import logic.function.iterate
import data.list.range

variables {n : ℕ}

@[simp] lemma equiv.symm_swap {α : Type*} [decidable_eq α] {x y : α} :
  equiv.symm (equiv.swap x y) = equiv.swap x y := rfl

@[simp] lemma equiv.perm.symm_one {α : Type*} [decidable_eq α] :
  equiv.symm (1 : equiv.perm α) = 1 := rfl

lemma equiv.perm.symm_mul {α : Type*} {f g : equiv.perm α} :
  (f * g).symm = g.symm * f.symm :=
mul_inv_rev f g

lemma nat.succ.commute_self : function.commute nat.succ nat.succ := function.commute.refl nat.succ

lemma function.succ_iterate {α : Type*} (f : α → α) (n : ℕ) : f^[n.succ] = f ∘ (f^[n]) :=
begin
  induction n with n hn,
  { simp only [function.iterate_one, function.comp.right_id, function.iterate_zero] },
  { rw [function.iterate_succ, hn],
    refine congr_arg (function.comp f) _,
    simpa only }
end

lemma nat.lt_iterate_succ (a : ℕ) (p : ℕ) : a < (nat.succ^[p + 1] a) :=
begin
  induction p with p hp,
  { exact nat.lt_succ_self a },
  { refine lt_trans hp _,
    simp only [function.succ_iterate],
    exact nat.lt_succ_self _ },
end

lemma list.range_lt (i : ℕ) {ix : ℕ} (h : ix < (list.range i).length) :
  (list.range i).nth_le ix h < i :=
by { convert h; simp }

def up_swap_fin (i : fin n) : fin (n + 1) ≃ fin (n + 1) := equiv.swap i.cast_succ i.succ

-- Swaps from 0 to (i + 2) are product of 01, 12, ..., (i + 1) (i + 2),
-- followed by i (i + 1), ..., 12, 01
def up_swaps_aux : ℕ → equiv.perm (fin (n + 2))
| 0 := 1
| (nat.succ i) := if h : i + 1 < n + 2
  then equiv.swap ⟨i, nat.lt_of_succ_lt h⟩ ⟨i.succ, h⟩ * up_swaps_aux i
  else 1


@[simp] lemma up_swaps_aux_zero :
  up_swaps_aux 0 = equiv.refl (fin (n + 2)) := rfl

@[simp] lemma up_swaps_aux_one :
  up_swaps_aux 1 = equiv.swap (0 : fin (n + 2)) 1 := rfl

@[simp] lemma up_swaps_aux_apply_zero {i : ℕ} (h : i < n + 2) :
  up_swaps_aux i 0 = ⟨i, h⟩ :=
begin
  induction i with i IH,
  { simpa only [up_swaps_aux_zero, id.def, equiv.coe_refl] },
  { simp only [up_swaps_aux, equiv.perm.mul_apply, dif_pos h,
               IH (nat.lt_of_succ_lt h), equiv.swap_apply_left] }
end

@[simp] lemma up_swaps_aux_symm_apply_zero {i : ℕ} (h : i + 1 < n + 2) :
  equiv.symm (up_swaps_aux i.succ) 0 = (1 : fin (n + 2)) :=
begin
  induction i with i IH,
  { simp only [up_swaps_aux_one, equiv.swap_apply_left, equiv.symm_swap] },
  {
    have hi : i + 1 < n + 2 := nat.lt_of_succ_lt h,
    have ns : (0 : fin (n + 2)) ≠ ⟨i.succ, hi⟩,
      from ne_of_lt (fin.mk_succ_pos i (nat.lt_of_succ_lt_succ hi)),
    have ns2 : (0 : fin (n + 2)) ≠ ⟨i.succ.succ, h⟩,
      from ne_of_lt (fin.mk_succ_pos i.succ (nat.lt_of_succ_lt_succ h)),
    rw [up_swaps_aux, dif_pos h, equiv.perm.symm_mul, equiv.perm.mul_apply,
        equiv.symm_swap, equiv.swap_apply_of_ne_of_ne ns ns2, IH hi] }
end

@[simp] lemma up_swaps_aux_apply_greater {i : ℕ} (h : i < n + 2) {x : fin (n + 2)}
  (h' : i < x) :
  up_swaps_aux i x = x :=
begin
  induction i with i IH,
  { simp only [up_swaps_aux_zero, id.def, equiv.coe_refl] },
  { simp only [up_swaps_aux, dif_pos h],
    have hi : i < n + 2 := nat.lt_of_succ_lt h,
    have : i < x,
      { refine lt_trans _ h',
        exact lt_add_one i },
    rw [equiv.perm.mul_apply, IH hi this, equiv.swap_apply_of_ne_of_ne],
    { exact ne_of_gt this },
    { exact ne_of_gt h' } }
end

@[simp] lemma up_swaps_aux_apply_self (i : ℕ) (h : i < n + 1) :
  up_swaps_aux i.succ (fin.succ ⟨i, h⟩) = fin.cast_succ ⟨i, h⟩ :=
begin
  cases i,
  { simpa only [up_swaps_aux_zero, id.def, equiv.coe_refl] },
  { simp only [up_swaps_aux, equiv.perm.mul_apply,
               dif_pos (nat.succ_lt_succ h), dif_pos (nat.lt_succ_of_lt h)],
    have : i < n + 2 := nat.lt_of_succ_lt (nat.lt_succ_of_lt h),
    have hi : i < (fin.succ ⟨i.succ, h⟩),
      { refine (nat.lt_succ_self i).trans _,
        exact lt_add_one (nat.succ i) },
    rw up_swaps_aux_apply_greater this hi,
    rw @equiv.swap_apply_of_ne_of_ne (fin (n + 2)) _ ⟨i, this⟩,
    { have : fin.succ ⟨i.succ, h⟩ = ⟨i.succ.succ, nat.succ_lt_succ h⟩ := rfl,
      simp only [this, equiv.swap_apply_right],
      rw fin.eq_iff_veq,
      simp only [fin.val_eq_coe, fin.coe_cast_succ, fin.coe_mk] },
    { rw fin.ne_iff_vne,
      refine ne_of_gt hi },
    { rw fin.ne_iff_vne,
      simp only [fin.val_eq_coe, fin.coe_succ, ne.def, fin.coe_mk],
      exact ne_of_gt (nat.lt_succ_self i.succ) } }
end

@[simp] lemma up_swaps_aux_apply_lt (i : ℕ) (h : i < n + 2)
  (x : fin (n + 1)) (h' : x.succ ≤ ⟨i, h⟩) : up_swaps_aux i x.succ = x.cast_succ :=
begin
  rcases i with _|i,
  { exact absurd h' (not_le_of_lt (fin.succ_pos x)) },
  induction i with i IH,
  { rcases eq_or_lt_of_le (fin.zero_le x) with rfl|H,
    { simp only [up_swaps_aux_one, fin.cast_succ_zero,
                 equiv.swap_apply_right, fin.succ_zero_eq_one] },
    { refine absurd H (not_lt_of_le _),
      rw ←fin.succ_le_succ_iff,
      exact h' } },
  { simp only [up_swaps_aux, equiv.perm.mul_apply, dif_pos h,
               dif_pos (nat.lt_of_succ_lt h)],
    cases eq_or_lt_of_le h' with H H,
    { have : i < x.succ,
      { simp only [H, fin.coe_mk],
        exact (nat.lt_add_of_zero_lt_left i 2 nat.succ_pos') },
      rw up_swaps_aux_apply_greater (nat.lt_of_succ_lt (nat.lt_of_succ_lt h)) this,
      rw @equiv.swap_apply_of_ne_of_ne (fin (n + 2)) _ _ _ x.succ,
      simp only [H, equiv.swap_apply_right],
      { rw [fin.eq_mk_iff_coe_eq, fin.coe_succ, nat.succ_inj'] at H,
        simp only [fin.eq_iff_veq, ←H, fin.val_eq_coe, fin.coe_cast_succ] },
      { exact ne_of_gt this },
      { simp only [H, subtype.mk_eq_mk, ne.def],
        exact nat.succ_ne_self i } },
    { have : x.succ ≤ ⟨i.succ, nat.lt_of_succ_lt h⟩,
        { simpa only [fin.lt_iff_coe_lt_coe, fin.le_iff_coe_le_coe,
                      fin.coe_mk, nat.lt_succ_iff] using H },
      specialize IH (nat.lt_of_succ_lt h) this,
      simp only [up_swaps_aux, dif_pos (nat.lt_of_succ_lt h), equiv.perm.mul_apply] at IH,
      rw [IH, equiv.swap_apply_of_ne_of_ne],
      { exact ne_of_lt (lt_of_lt_of_le (fin.cast_succ_lt_succ x) this) },
      { exact ne_of_lt (lt_trans (fin.cast_succ_lt_succ x) H) } } }
end

def up_swaps' : ℕ → equiv.perm (fin (n + 2))
| 0 := 1
| (nat.succ i) :=
  if h : i + 1 < n + 2
  then up_swaps_aux i.succ * (equiv.symm (up_swaps_aux i))
  else 1

def up_swaps (i : fin (n + 2)) : equiv.perm (fin (n + 2)) := up_swaps' i

def up_swaps_list' (i : ℕ) : list (ℕ × ℕ) := (list.range i).map (λ x, (x, x.succ))

#eval up_swaps_list' 4

def up_swaps_list : ℕ → list (ℕ × ℕ)
| 0 := []
| (nat.succ i) := up_swaps_list' i.succ ++ (up_swaps_list' i).reverse

def up_swaps_map : ℕ → list (ℕ ≃ ℕ)
| 0 := []
| (nat.succ i) := (up_swaps_list i.succ).map (λ pair, equiv.swap pair.fst pair.snd)

#eval (list.range 10).map((up_swaps_map 3).prod)

@[simp] lemma up_swaps_zero : up_swaps 0 = equiv.refl (fin (n + 2)) := rfl

@[simp] lemma up_swaps_one : up_swaps 1 = equiv.swap (0 : fin (n + 2)) 1 := rfl

lemma up_swaps_symm' (i : fin (n + 2)) : (up_swaps i) = equiv.swap 0 i :=
begin
  obtain ⟨i, hi⟩ := i,
  rcases i with _|i,
  { simp only [equiv.swap_self, fin.mk_zero, up_swaps_zero] },
  induction i with i IH,
  { simp only [up_swaps_one, fin.mk_one] },
  {
    specialize IH (nat.lt_of_succ_lt hi),
    simp only [up_swaps, up_swaps', dif_pos (nat.lt_of_succ_lt hi), dif_pos,
               fin.mk_eq_subtype_mk, fin.coe_mk] at IH,
    -- rw equiv.apply_eq_iff_eq_symm_apply at IH,
    simp only [up_swaps, up_swaps', dif_pos hi, up_swaps_aux,
               dif_pos (nat.lt_of_succ_lt hi), dif_pos, fin.mk_eq_subtype_mk, fin.coe_mk],
    rw equiv.perm.symm_mul,
    ext x,
    rw [fin.coe_eq_val, fin.coe_eq_val, ←fin.eq_iff_veq],
    by_cases h : x = 0,
    { rcases i with _|_|i,
      { cases n,
        { exact absurd hi (lt_irrefl 2) },
        { have c1 : fin.cast_succ (1 : fin (n + 2)) = 1 := rfl,
          have : (1 : fin (n + 2)).succ ≠ 1 := by convert (fin.succ_succ_ne_one 0),
          simpa [c1, h, equiv.swap_apply_of_ne_of_ne (fin.succ_ne_zero 1) this] } },
      {
        have : nat.succ 1 = 2 := rfl,
        simp only [h, nat.nat_zero_eq_zero, up_swaps_aux_one, equiv.swap_apply_left, equiv.symm_swap, fin.mk_one, equiv.perm.mul_apply],
        rw @equiv.swap_apply_of_ne_of_ne (fin (n + 2)) _ _ _ 0,
        rw equiv.swap_apply_left,
        rw @equiv.swap_apply_of_ne_of_ne (fin (n + 2)) _ _ _ 1,
        rw equiv.swap_apply_right,
        simp [this],
      },
        have hi' : i + 1 < n + 2,
          { refine (lt_trans _ hi),
            exact nat.lt_iterate_succ _ 1 },
        have hi'' : i + 2 < n + 2,
          { refine (lt_trans _ hi),
            exact nat.lt_iterate_succ _ 0 },
        have ni : (0 : fin (n + 2)) ≠ ⟨i.succ, hi'⟩ := ne_of_lt (fin.mk_succ_pos i (nat.lt_of_succ_lt_succ hi')),
        have ni' : (0 : fin (n + 2)) ≠ ⟨i.succ.succ, hi''⟩ := ne_of_lt (fin.mk_succ_pos i.succ (nat.lt_of_succ_lt_succ hi'')),
    },
    {  },
  }
end

lemma up_swaps_symm (i : fin (n + 2)) : (up_swaps i) = equiv.swap 0 i :=
begin
  rcases i with _|_|i,
  { simp only [equiv.swap_self, fin.mk_zero, up_swaps_zero] },
  { simp only [up_swaps_one, fin.mk_one] },
  {
  }
end

#eval up_swaps' 2 (0 : fin 5)

lemma up_swaps_apply_zero (i : fin (n + 2)) : up_swaps i 0 = i :=
begin
  cases n,
  { fin_cases i,
    { simp only [id.def, equiv.coe_refl, up_swaps_zero] },
    { simp only [equiv.swap_apply_left, up_swaps_one] } },
  have : fin.cast_succ (1 : fin (n + 2)) = 1 := rfl,
  rcases i with _|_|_|i,
  { simp },
  { simp },
  { simp [up_swaps, up_swaps', this],
    rw ←fin.succ_zero_eq_one,
    rw up_swaps_aux_apply_lt,
    rw equiv.swap_apply_of_ne_of_ne,
    { simp [fin.eq_iff_veq, fin.coe_one, fin.val_eq_coe, fin.coe_succ] },
    { exact ne_of_gt (fin.succ_pos 1) },
    { exact this ▸ ne_of_gt (fin.cast_succ_lt_succ 1) } },
  have l1 : 1 < i.succ.succ := nat.succ_lt_succ (nat.succ_pos i),
  have gc : fin.cast_succ ⟨i.succ.succ, nat.lt_of_succ_lt_succ i_property⟩ > 1 := l1,
  have ns : fin.succ ⟨i.succ.succ, nat.lt_of_succ_lt_succ i_property⟩ ≠ 1,
    { exact ne_of_gt (lt_trans gc (fin.cast_succ_lt_succ _)) },
  simp only [up_swaps, up_swaps', i_property, nat.lt_of_succ_lt i_property, equiv.swap_apply_of_ne_of_ne, ns.symm, ne_of_lt gc,
 up_swaps_aux_symm_apply_zero, dif_pos, fin.mk_eq_subtype_mk, ne.def, not_false_iff, fin.coe_mk, equiv.perm.mul_apply],
  rw ←fin.succ_zero_eq_one,
  rw up_swaps_aux_apply_lt,
  -- { obtain ⟨i, hi⟩ := i,
  --   rcases i with _|i,
  --   { simp only [fin.mk_zero, id.def, equiv.coe_refl, up_swaps_zero] },
  --   induction i with i IH,
  --   { simp only [equiv.swap_apply_left, up_swaps_one, fin.mk_one] },
  --   {
  --     have hi' : i + 1 < n + 3 := nat.lt_of_succ_lt hi,
  --     rw [up_swaps],
  --     rw [fin.coe_mk, up_swaps'],
  --     rw dif_pos hi,
  --     simp only [equiv.perm.mul_apply, hi', up_swaps_aux_symm_apply_zero, fin.mk_eq_subtype_mk],
  --     rcases lt_trichotomy i.succ 1 with H|H|H,
  --     { refine absurd (nat.lt_of_succ_lt_succ H) (not_lt_of_le i.zero_le) },
  --     { have : fin.cast_succ (1 : fin (n + 2)) = 1 := rfl,
  --       simp only [H, this, up_swaps_aux_one, equiv.swap_apply_left, fin.mk_one],
  --       rw [equiv.swap_apply_of_ne_of_ne],
  --       { simp [fin.eq_iff_veq, fin.coe_one, fin.val_eq_coe, fin.coe_succ] },
  --       { exact ne_of_gt (fin.succ_pos 1) },
  --       { exact this ▸ ne_of_gt (fin.cast_succ_lt_succ 1) } },
  --     specialize IH hi',
  --     simp [up_swaps, up_swaps', hi'] at IH,
  --     -- rw equiv.apply_eq_iff_eq_symm_apply at IH,
  --     rw [up_swaps],
  --     rw [fin.coe_mk, up_swaps'],
  --     rw dif_pos hi,
  --     simp only,
  --     simp [hi, nat.lt_of_succ_lt hi],
  --     {  },
  --     rw up_swaps_aux,
  --     rw up_swaps_aux_symm_apply_zero (nat.lt_of_succ_lt hi),
  --   } },
end

-- lemma up_swaps_succ_succ (i : fin n) : up_swaps i.succ.succ =
--   up_swaps i.succ.cast_succ * equiv.swap i.succ.cast_succ i.succ.succ
--     * equiv.symm (up_swaps i.succ.cast_succ) :=
-- begin
--   obtain ⟨i, hi⟩ := i,
--   induction i with i IH,
--   { ext x,
--     by_cases h : x = 0,
--     simp [h],
--     simp },
-- end
