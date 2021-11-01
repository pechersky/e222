import lecture02

namespace e222
open e222.group

variables {G : Type*} [group G]

-- 2.15
example {x y z : G} (h : x ᵍ* y ᵍ* z = ᵍ1) :
  y ᵍ* z ᵍ* x = ᵍ1 :=
begin
  suffices : xᵍ⁻¹ ᵍ* x ᵍ* y ᵍ* z ᵍ* x = xᵍ⁻¹ ᵍ* ᵍ1 ᵍ* x,
    { simpa },
  refine congr_arg (λ t, t ᵍ* x) _,
  rw [←group.mul_assoc, ←group.mul_assoc, group.mul_assoc x],
  exact congr_arg (λ t, xᵍ⁻¹ ᵍ* t) h
end

example {x y z : G} (h : x ᵍ* y ᵍ* z = ᵍ1) :
  y ᵍ* x ᵍ* z = ᵍ1 ↔ (x ᵍ* z = z ᵍ* x) :=
begin
  suffices : xᵍ⁻¹ ᵍ* x ᵍ* y ᵍ* z ᵍ* x = xᵍ⁻¹ ᵍ* ᵍ1 ᵍ* x,
    { simp only [group.mul_one, group.inv_mul, group.one_mul] at this,
      rw [←this, ←group.mul_assoc, ←group.mul_assoc, group.mul_left_inj] },
  refine congr_arg (λ t, t ᵍ* x) _,
  rw [←group.mul_assoc, ←group.mul_assoc, group.mul_assoc x],
  exact congr_arg (λ t, xᵍ⁻¹ ᵍ* t) h
end

-- 2.1.7
example {S : Type*} : associative (λ (a b : S), a) :=
begin
  intros a b c,
  dsimp,
  refl
end

-- 2.2.1

namespace p221

abbreviation M : matrix (fin 2) (fin 2) ℤ := ![![1, 1], ![-1, 0]]

@[simp] lemma M_def : M = ![![1, 1], ![-1, 0]] := rfl

lemma h2 : M ^ 2 = ![![0, 1], ![-1, -1]] :=
by { rw pow_two, simp }

lemma h3 : M ^ 3 = -1 :=
begin
  rw [pow_bit1, ←pow_bit0, h2],
  suffices : (![![(-1 : ℤ), 0], ![0, -1]] : matrix _ _ ℤ) = (-1 : matrix _ _ ℤ),
  { simpa },
  ext i j,
  fin_cases i;
  fin_cases j;
  norm_num
end

lemma h4 : M ^ 4 = -M :=
by rw [pow_succ', h3, neg_mul_eq_neg_mul_symm, _root_.one_mul]

lemma h5 : M ^ 5 = -M ^ 2 :=
by rw [(show 5 = 3 + 2, by norm_num), pow_add, h3, neg_mul_eq_neg_mul_symm, _root_.one_mul]

lemma h6 : M ^ 6 = 1 :=
by rw [pow_bit0, h3, neg_mul_neg, _root_.one_mul]

lemma hinv : M * M ^ 5 = 1 :=
by rw [←pow_succ, h6]

abbreviation M' : GLₙ 2 ℤ := (⟨M, M ^ 5, hinv, matrix.nonsing_inv_right_left hinv⟩ : GLₙ 2 ℤ)

lemma ho : order_of M' = 6 :=
begin
  rw [order_of, function.minimal_period, dif_pos, nat.find_eq_iff],
  { simp only [units.ext_iff, is_periodic_pt_mul_iff_pow_eq_one, h6, true_and, nat.succ_pos',
               exists_prop, gt_iff_lt, units.coe_mk, not_and, eq_self_iff_true, units.coe_one,
               units.coe_pow],
    intros n hn npos H,
    interval_cases n,
    { simpa using congr_fun (congr_fun H 1) 1 },
    { simpa [h2] using congr_fun (congr_fun H 0) 0 },
    { simpa [h3] using congr_fun (congr_fun H 0) 0 },
    { simpa [h4] using congr_fun (congr_fun H 1) 1 },
    { simpa [h5, h2] using congr_fun (congr_fun H 0) 0 } },
  { refine ⟨6, by simp, _⟩,
    simp [is_periodic_pt_mul_iff_pow_eq_one, units.ext_iff, h6] }
end

lemma units.exists_coe_gpow_iff_exists_coe_pow_of_order_of_pos {α : Type*} [monoid α]
  {x : units α} {y : α} (h : 0 < order_of x) :
  (∃ (z : ℤ), ↑(x ^ z) = y) ↔ (∃ (k : ℕ), ↑(x ^ k) = y) :=
begin
  split,
  { rintro ⟨z, rfl⟩,
    induction z using int.induction_on with z IH z IH,
    { use 0,
      simp },
    { simp [←int.coe_nat_succ] },
    { have : (↑x⁻¹ : α) = (x ^ (order_of x - 1) : units α),
      { rw [←units.ext_iff, ←mul_right_inj x, mul_right_inv, ←pow_succ,
            nat.sub_add_cancel, pow_order_of_eq_one],
        exact nat.succ_le_iff.mpr h },
      obtain ⟨k, hk⟩ := IH,
      simp only [zpow_neg, units.coe_pow, zpow_coe_nat] at hk,
      use (k + (order_of x - 1)),
      simp [zpow_sub_one, this, ←hk, pow_add] } },
  { rintro ⟨k, rfl⟩,
    use k,
    simp },
end

example : (subgroup.zpowers M').carrier.image (units.coe_hom _)
  = { 1, ![![(1 : ℤ), 1], ![-1, 0]], ![![0, 1], ![-1, -1]],
      -1, ![![-1, -1], ![1, 0]], ![![0, -1], ![1, 1]] } :=
begin
  ext N,
  simp_rw [set.mem_image, subgroup.mem_carrier, subgroup.mem_zpowers_iff],
  simp only [set.mem_insert_iff, set.mem_singleton_iff, exists_exists_eq_and,
             units.coe_hom_apply],
  rw units.exists_coe_gpow_iff_exists_coe_pow_of_order_of_pos,
  { split,
    { rintro ⟨k, hk⟩,
      rw [pow_eq_mod_order_of, ho, units.coe_pow] at hk,
      subst hk,
      set n : ℕ := k % 6 with hn,
      have hless : n < 6,
      { refine nat.mod_lt _ _,
        simp },
      interval_cases n with hn';
      simp [hn', h2, h3, h4, h5] },
    { rintro (rfl|rfl|rfl|rfl|rfl|rfl),
      { use 0,
        rw [pow_zero, units.coe_one] },
      { use 1,
        rw [pow_one, units.coe_mk, M_def] },
      { use 2,
        simp only [h2, units.coe_mk, units.coe_pow] },
      { use 3,
        simp only [h3, units.coe_mk, units.coe_pow] },
      { use 4,
        rw [units.coe_pow, units.coe_mk, h4, neg_eq_iff_neg_eq, M_def],
        simp only [matrix.neg_cons, neg_neg, neg_zero, matrix.neg_empty] },
      { use 5,
        rw [units.coe_pow, units.coe_mk, h5, h2, neg_eq_iff_neg_eq],
        simp only [matrix.neg_cons, neg_neg, neg_zero, matrix.neg_empty] } } },
  { rw ho,
    simp },
end

end p221

-- 2.2.15a
example {G : Type*} [group G] {H : subgroup G} (e' : G) (he : e' ∈ H)
  (he' : ∀ h ∈ H, e' ᵍ* h = h) (he'' : ∀ h ∈ H, h ᵍ* e' = h) :
  e' = ᵍ1 :=
begin
  rw [←mul_left_inj e'ᵍ⁻¹, he'', group.mul_one],
  rwa subgroup.mem_inv_iff,
end
-- 2.2.15b
example {G : Type*} [group G] {H : subgroup G} (g g' : G) (hg : g ∈ H) (hg' : g' ∈ H)
  (h : g ᵍ* g' = ᵍ1) (h' : g' ᵍ* g = ᵍ1) : g' = gᵍ⁻¹ :=
begin
  rw [←mul_left_inj g, h, group.mul_inv]
end

end e222

lemma pow_eq_one_iff_order_of_dvd_of_ne_one {G : Type*} [group G] {g : G} {n : ℕ} (h : g ≠ 1) :
  g ^ n = 1 ↔ order_of g ∣ n :=
begin
  exact order_of_dvd_iff_pow_eq_one.symm
end

-- 2.2.20(a)
example {G : Type*} [comm_group G] (a b : G) :
  order_of (a * b) ∣ (nat.lcm (order_of a) (order_of b)) :=
begin
  have ha : a ^ ((order_of a).lcm (order_of b)) = 1,
  { obtain ⟨k, hk⟩ : order_of a ∣ (order_of a).lcm (order_of b) := nat.dvd_lcm_left _ _,
    rw [hk, pow_mul, pow_order_of_eq_one, one_pow] },
  have hb : b ^ ((order_of a).lcm (order_of b)) = 1,
  { obtain ⟨k, hk⟩ : order_of b ∣ (order_of a).lcm (order_of b) := nat.dvd_lcm_right _ _,
    rw [hk, pow_mul, pow_order_of_eq_one, one_pow] },
  rwa [←mul_left_inj (b ^ ((order_of a).lcm (order_of b))), ←mul_pow, hb, one_mul,
       ←order_of_dvd_iff_pow_eq_one] at ha
end
