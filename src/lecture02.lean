import lecture01
import data.complex.basic
import data.equiv.fintype
import data.int.order
import tactic.norm_swap

namespace e222

namespace group

variables {n : ℕ}

example : GLₙ n ℝ = units (matrix (fin n) (fin n) ℝ) := rfl
example : GLₙ n ℂ = units (matrix (fin n) (fin n) ℂ) := rfl
example : GLₙ n ℚ = units (matrix (fin n) (fin n) ℚ) := rfl

variables {G : Type*} [group G] (a b c : G)

example : a ᵍ* (b ᵍ* c) = a ᵍ* b ᵍ* c := group.mul_assoc _ _ _
example : ᵍ1 ᵍ* a = a ∧ a ᵍ* ᵍ1 = a := ⟨group.one_mul _, group.mul_one _⟩
example : a ᵍ* aᵍ⁻¹ = ᵍ1 ∧ aᵍ⁻¹ ᵍ* a = ᵍ1 := ⟨group.mul_inv _, group.inv_mul _⟩

-- Matrices that are invertible form a group under matrix multiplication
noncomputable instance {K n' : Type*} [comm_ring K] [fintype n'] [decidable_eq n'] :
  group (units (matrix n' n' K)) :=
{ op := (*),
  assoc' := λ _ _ _, units.ext $
    by simp only [units.coe_mul, matrix.mul_eq_mul, ←matrix.mul_assoc],
  e := 1,
  op_e' := λ _, units.ext $ by
    by simp only [units.coe_mul, units.coe_one, matrix.mul_eq_mul, matrix.mul_one],
  e_op' := λ _, units.ext $ by
    by simp only [units.coe_mul, units.coe_one, matrix.mul_eq_mul, matrix.one_mul],
  inv := λ a, ⟨a⁻¹, a,
    by rw [matrix.mul_eq_mul, matrix.nonsing_inv_mul _
           ((matrix.is_unit_iff_is_unit_det _).mp a.is_unit)],
    by rw [matrix.mul_eq_mul, matrix.mul_nonsing_inv _
           ((matrix.is_unit_iff_is_unit_det _).mp a.is_unit)]⟩,
  inv_op' := λ x, units.ext $ by
    rw [units.coe_mul, units.coe_mk, units.coe_one,
        matrix.mul_eq_mul, matrix.nonsing_inv_mul _
        ((matrix.is_unit_iff_is_unit_det _).mp x.is_unit)],
  op_inv' := λ x, units.ext $ by
    rw [units.coe_mul, units.coe_mk, units.coe_one,
        matrix.mul_eq_mul, matrix.mul_nonsing_inv _
        ((matrix.is_unit_iff_is_unit_det _).mp x.is_unit)] }

-- Transfer the group instance to our notation
noncomputable instance (n : ℕ) (K : Type*) [comm_ring K] : group (GLₙ n K) :=
by apply_instance

lemma GLₙ.group.e_def {K : Type*} [comm_ring K] : (GLₙ.group n K).e = 1 := rfl
lemma GLₙ.group.op_def {K : Type*} [comm_ring K] : (GLₙ.group n K).op = (*) := rfl
lemma GLₙ.group.inv_coe {K : Type*} [comm_ring K] (M : GLₙ n K) :
  (↑(Mᵍ⁻¹ : GLₙ n K) : matrix (fin n) (fin n) K) = (↑M : matrix _ _ _)⁻¹ := rfl

-- Our own notation
notation `Sym ` T := T ≃ T
notation `Aut ` T := T ≃ T

-- The prototypical (ur) example of a group is the symmetries of T
-- defined so that `(f * g)(x) = f(g(x))`
instance (T : Type*) : group (Sym T) :=
{ op := λ f g, g.trans f,
  assoc' := λ _ _ _, equiv.trans_assoc _ _ _,
  e := equiv.refl _,
  op_e' := equiv.trans_refl,
  e_op' := equiv.refl_trans,
  inv := equiv.symm,
  inv_op' := equiv.trans_symm,
  op_inv' := equiv.symm_trans }

-- helper lemmas to associate symmetry multiplication with application
@[simp] lemma mul_apply {T : Type*} (f g : Sym T) (x : T) :
  (f ᵍ* g) x = f (g x) := rfl

lemma equiv.group.op_def (T : Type*) : (equiv.group T).op = (*) := rfl
lemma equiv.group.e_def (T : Type*) : (equiv.group T).e = 1 := rfl
lemma equiv.group.inv_def {T : Type*} (x : Sym T) : xᵍ⁻¹ = x⁻¹ := rfl

-- Definition of subgroup, similar to the mathlib construction
@[ext] structure subgroup (G : Type*) [group G] :=
-- subset
(carrier : set G)
-- contains identity
(mem_e : ᵍ1 ∈ carrier)
-- closed under multiplication
(mem_op : ∀ ⦃x : G⦄ (hx : x ∈ carrier) ⦃y : G⦄ (hy : y ∈ carrier), x ᵍ* y ∈ carrier)
-- closed under inverses
(mem_inv : ∀ ⦃x : G⦄ (hx : x ∈ carrier), xᵍ⁻¹ ∈ carrier)

-- Notational shortcut
instance : has_mem G (subgroup G) := ⟨λ g H, g ∈ H.carrier⟩

-- Normalization to express membership using the notational shortcut
@[simp] lemma subgroup.mem_iff {g : G} {H : subgroup G} : g ∈ H.carrier ↔ g ∈ H := iff.rfl

-- Two subgroups are equal iff they are equal on all elements (extensionality)
lemma subgroup.ext_iff' {G : Type*} [group G] {H H' : subgroup G} :
  H = H' ↔ (∀ (g : G), g ∈ H ↔ g ∈ H') :=
begin
  split,
  { intro H,
    rw H,
    exact λ _, iff.rfl },
  { intro h,
    ext,
    simp only [h, subgroup.mem_iff] },
end

@[simp] lemma mul_left_inj (x : G) {y z : G} :
  x ᵍ* y = x ᵍ* z ↔ y = z :=
⟨λ h, by simpa [mul_assoc] using congr_arg (λ t, xᵍ⁻¹ ᵍ* t) h, λ h, h ▸ rfl⟩

@[simp] lemma mul_right_inj (y : G) {x z : G} :
  x ᵍ* y = z ᵍ* y ↔ x = z :=
⟨λ h, by simpa [←mul_assoc] using congr_arg (λ t, t ᵍ* yᵍ⁻¹) h, λ h, h ▸ rfl⟩

@[simp] lemma inv_inv (g : G) :
  gᵍ⁻¹ᵍ⁻¹ = g :=
begin
  rw [←mul_left_inj gᵍ⁻¹, mul_inv, inv_mul]
end

@[simp] lemma subgroup.mem_inv_iff {x : G} {H : subgroup G} :
  xᵍ⁻¹ ∈ H ↔ x ∈ H :=
begin
  refine ⟨λ h, _, λ h, H.mem_inv h⟩,
  rw ←inv_inv x,
  exact H.mem_inv h
end

-- GLₙ(ℝ) as a subgroup of Sym(ℝ^n)
example {n : ℕ} : subgroup (Sym (fin n → ℝ)) :=
{ carrier := {f | is_linear_map ℝ f}, -- we know that GLₙ(ℝ) is the set of linear maps
  mem_e := by { simp only [equiv.perm.coe_one, set.mem_set_of_eq,
    show (ᵍ1 : Sym (fin n → ℝ)) = 1, from rfl],
    exact ⟨by simp, by simp⟩ },
  mem_op := by { simp_rw [set.mem_set_of_eq],
    intros f hf g hg,
    refine ⟨λ x y, _, λ r x, _⟩,
    { simp only [mul_apply, hg.map_add, hf.map_add] },
    { simp only [mul_apply, hg.map_smul, hf.map_smul] } },
  mem_inv := by { simp_rw [set.mem_set_of_eq],
      -- show (equiv.group (fin n → ℝ)).inv = equiv.symm, from rfl],
    intros f hf,
    refine ⟨λ x y, _, λ r x, _⟩;
    { apply f.injective,
      simp only [hf.map_add, hf.map_smul, ←mul_apply, equiv.group.op_def,
        mul_inv, equiv.group.e_def, equiv.perm.coe_one, id.def] } } }

-- order of Sₙ is n!
example {n : ℕ} : fintype.card (Sₙ n) = nat.factorial n :=
begin
  rw [fintype.card_perm, fintype.card_fin]
end

-- S₁ is solely the identity
-- we can rely on mathlib to enumerate the elements for us
-- using a brute-force computation, invoked by `dec_trivial`
-- because it is decidable to check equality of finite perms,
-- by checking on all the elements
example : (finset.univ : finset Sₙ 1) = {1} := dec_trivial

example : (finset.univ : finset Sₙ 2) = {1, equiv.swap 0 1} := dec_trivial

-- TODO: use cycle notation
example : (finset.univ : finset Sₙ 3) =
  {1, equiv.swap 0 1, equiv.swap 0 2, equiv.swap 1 2,
    equiv.of_bijective ![1, 2, 0] dec_trivial, equiv.of_bijective ![2, 0, 1] dec_trivial} :=
  dec_trivial

-- TODO: #8258
@[simps apply symm_apply]
def fin_as_subtype {n m : ℕ} (h : n ≤ m) : fin n ≃o subtype (λ (i : fin m), (i : ℕ) < n) :=
{ to_fun := λ i, ⟨fin.cast_le h i, by simpa using i.is_lt⟩,
  inv_fun := λ i, ⟨i, i.prop⟩,
  left_inv := λ _, by simp,
  right_inv := λ _, by simp,
  map_rel_iff' := λ _ _, by simp }

-- TODO: #8259
def subgroup.Sk (k n : ℕ) (h : k ≤ n) : subgroup (Sₙ n) :=
{ carrier := set.range (λ f : Sₙ k, f.extend_domain (fin_as_subtype h).to_equiv),
  mem_e := by { simp only [set.mem_range], use 1,
    simp only [equiv.group.e_def, equiv.perm.extend_domain_one] },
  mem_op := by { simp only [forall_apply_eq_imp_iff', set.mem_range, forall_const,
    equiv.perm.extend_domain_mul, exists_imp_distrib, exists_apply_eq_apply, equiv.group.op_def] },
  mem_inv := by { simp only [forall_apply_eq_imp_iff', set.mem_range, forall_const,
    equiv.perm.extend_domain_inv, exists_imp_distrib, exists_apply_eq_apply, equiv.group.inv_def] } }

-- The group Sₙ is non-abelian for all 3 ≤ n
example {n : ℕ} (hn : 3 ≤ n) : ∃ (g h : Sₙ n), g ᵍ* h ≠ h ᵍ* g :=
begin
  obtain ⟨g, h, hgh⟩ : ∃ g h : Sₙ 3, g ᵍ* h ≠ h ᵍ* g,
  { use [equiv.swap 0 1, equiv.swap 0 2],
    intro H,
    have := equiv.congr_fun H 0,
    norm_num [equiv.group.op_def] at this },
  refine ⟨g.extend_domain (fin_as_subtype hn).to_equiv,
          h.extend_domain (fin_as_subtype hn).to_equiv, λ H, hgh _⟩,
  ext x,
  simpa [equiv.perm.extend_domain_mul, -rel_iso.coe_fn_to_equiv,
    equiv.perm.extend_domain_apply_image, ←subtype.ext_iff, ←fin.ext_iff] using
    congr_arg (λ (p : Sₙ n), p ((fin_as_subtype hn).to_equiv x)) H
end

-- Subgroup of GL₂(ℝ) which stabilizer the line `y = 0`
noncomputable example : subgroup (GLₙ 2 ℝ) :=
{ carrier := {A : GLₙ 2 ℝ | ∃ (a c d : ℝ), a * d ≠ 0 ∧ ![![a, c], ![0, d]] = (↑A : matrix _ _ _)},
  mem_e := by { simp only [units.coe_one, ne.def, set.mem_set_of_eq, mul_eq_zero, GLₙ.group.e_def],
  use [1, 0, 1],
  simp only [not_false_iff, one_ne_zero, or_self, true_and],
  ext i j,
  fin_cases i;
  fin_cases j;
  simp },
  mem_op := by { simp only [and_imp, ne.def, matrix.mul_eq_mul, set.mem_set_of_eq, mul_eq_zero,
    exists_imp_distrib, units.coe_mul, not_or_distrib, GLₙ.group.op_def],
    intros M a c d ha hd hM M' a' c' d' ha' hd' hM',
    use [a * a', a * c' + c * d', d * d'],
    simp [←hM, ←hM', ha, hd, ha', hd'] },
  mem_inv := by { simp only [not_or_distrib, and_imp, ne.def, set.mem_set_of_eq, exists_imp_distrib,
    mul_eq_zero],
    intros M a c d ha hd hM,
    suffices : (↑M : matrix _ _ _) * ![![a⁻¹, - c / (a * d)], ![0, d⁻¹]] = 1,
    { use [a⁻¹, - c / (a * d), d⁻¹],
      rw [matrix.mul_eq_mul] at this,
      simp [ha, hd, GLₙ.group.inv_coe, matrix.inv_eq_right_inv this] },
    rw ←hM,
    ext i j,
    fin_cases i;
    fin_cases j;
    { field_simp [ha, hd],
      try { ring } } } }

instance : group ℤ :=
{ op := (+),
  assoc' := λ _ _ _, (int.add_assoc _ _ _).symm,
  e := 0,
  op_e' := int.add_zero,
  e_op' := int.zero_add,
  inv := λ x, -x,
  inv_op' := int.add_left_neg,
  op_inv' := int.add_right_neg }

instance : abelian_group ℤ :=
{ comm := int.add_comm,
  ..int.group }

lemma int.group.op_def : int.group.op = (+) := rfl
lemma int.group.e_def : int.group.e = 0 := rfl
lemma int.group.inv_def (x : ℤ) : xᵍ⁻¹ = -x := rfl

def subgroup.int (b : ℤ) : subgroup ℤ :=
{ carrier := set.range ((*) b), -- left multiplication by b
  mem_e := by {
    simp only [set.mem_range, int.group.e_def],
    simp only [mul_eq_zero, exists_or_eq_right] },
  mem_op := by {
    simp only [set.mem_range, int.group.op_def],
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩,
    use (m + n),
    simp only [mul_add] },
  mem_inv := by {
    simp only [set.mem_range, int.group.inv_def],
    rintro _ ⟨m, rfl⟩,
    use -m,
    simp only [mul_neg_eq_neg_mul_symm] } }

lemma subgroup.int.mem_iff {b x : ℤ} :
  x ∈ subgroup.int b ↔ ∃ (m : ℤ), b * m = x := iff.rfl

@[simp] lemma inv_one (G : Type*) [group G] : (ᵍ1 : G)ᵍ⁻¹ = ᵍ1 :=
by rw [←mul_left_inj ᵍ1, mul_inv, mul_one]

-- The largest trivial subgroup
def subgroup.top (G : Type*) [group G] : subgroup G :=
{ carrier := set.univ,
  mem_e := by simp only [set.mem_univ],
  mem_op := by simp only [set.mem_univ, implies_true_iff],
  mem_inv := by simp only [set.mem_univ, implies_true_iff] }

@[simp] lemma subgroup.mem_top {G : Type*} [group G] (g : G) :
  g ∈ subgroup.top G :=
set.mem_univ g

-- The smallest trivial subgroup
def subgroup.bot (G : Type*) [group G] : subgroup G :=
{ carrier := {ᵍ1},
  mem_e := by simp only [set.mem_singleton],
  mem_op := by simp only [mul_one, set.mem_singleton_iff, forall_eq],
  mem_inv := by simp only [set.mem_singleton_iff, forall_eq, inv_one] }

@[simp] lemma subgroup.mem_bot_iff {G : Type*} [group G] {g : G} :
  g ∈ subgroup.bot G ↔ g = ᵍ1 :=
set.mem_singleton_iff

-- The smallest subgroup of ℤ is the trivial one
lemma subgroup.int_zero : subgroup.int 0 = subgroup.bot ℤ :=
begin
  simp_rw [subgroup.ext_iff', subgroup.int.mem_iff],
  intro,
  simp only [eq_comm, exists_const, int.group.e_def, subgroup.mem_bot_iff, zero_mul]
end

-- The largest subgroup of ℤ is the (* 1) one
lemma subgroup.int_one : subgroup.int 1 = subgroup.top ℤ :=
begin
  simp_rw [subgroup.ext_iff', subgroup.int.mem_iff],
  intro,
  simp [forall_const, one_mul, subgroup.mem_top, iff_self, nonempty_of_inhabited,
    exists_apply_eq_apply]
end

-- Multiples are part of int subgroups, like powers. Proved by induction
lemma subgroup.mem_left_mul (H : subgroup ℤ) ⦃m : ℤ⦄ (hm : m ∈ H) (b : ℤ) :
  b * m ∈ H :=
begin
  induction b using int.induction_on with b IH b IH,
  { rw [int.zero_mul, ←int.group.e_def],
    exact H.mem_e },
  { rw [add_mul, int.one_mul, ←int.group.op_def],
    exact H.mem_op IH hm },
  { rw [sub_mul, int.one_mul, int.sub_eq_add_neg, ←int.group.op_def, ←int.group.inv_def],
    exact H.mem_op IH (H.mem_inv hm) }
end

-- There are no other subgroups of ℤ other than the ones defined by subgroup.int
example (H : subgroup ℤ) : ∃ (b : ℤ), H = subgroup.int b :=
begin
  -- case 1: H = {0}
  by_cases h : H = subgroup.int 0,
  { exact ⟨0, h⟩ },
  -- case 2: H ≠ {0}, so contains m ≠ 0
  obtain ⟨m, hm', hm⟩ : ∃ (m : ℤ) (hm : m ≠ 0), m ∈ H,
  { contrapose! h,
    ext,
    simp only [subgroup.int_zero, subgroup.mem_bot_iff, subgroup.mem_iff],
    split,
    { intro h',
      contrapose! h,
      refine ⟨x, _, h'⟩,
      rwa ←int.group.e_def },
    { intro h',
      simpa [h'] using H.mem_e } },
  set bs : set ℤ := {b : ℤ | b ∈ H ∧ 0 < b} with hbs,
  have bdd : bdd_below bs,
  { use 0,
    simp only [mem_lower_bounds, and_imp, set.mem_set_of_eq],
    intros x _ H,
    exact H.le },
  have hmem : Inf bs ∈ bs,
  { refine int.cInf_mem _ bdd,
    cases hm'.lt_or_lt with mneg mpos,
    { use -m,
      simp only [set.mem_set_of_eq],
      split,
      { rwa [←int.group.inv_def, subgroup.mem_inv_iff] },
      { rwa [right.neg_pos_iff] } },
    { use m,
      simp only [set.mem_set_of_eq],
      exact ⟨hm, mpos⟩ } },
  nth_rewrite_rhs 0 hbs at hmem,
  rw [set.mem_set_of_eq] at hmem,
  use Inf bs,
  simp_rw [subgroup.ext_iff', subgroup.int.mem_iff],
  intros g,
  split,
  -- Show that `bℤ ⊆ H`
  { intros hg,
    use g / Inf bs,
    refine int.mul_div_cancel' _,
    refine int.dvd_of_mod_eq_zero _,
    have modnonneg : 0 ≤ g % Inf bs := int.mod_nonneg _ hmem.right.ne',
    -- = int.mod_nonneg _ hlb.right.ne',
    have modlt : g % Inf bs < (Inf bs) := int.mod_lt_of_pos _ hmem.right,
    contrapose! modlt,
    refine cInf_le bdd _,
    rw ←int.mod_add_div g (Inf bs) at hg,
    suffices : (Inf bs) * (g / Inf bs) ∈ H,
    { nth_rewrite_rhs 0 hbs,
      rw set.mem_set_of_eq,
      refine ⟨_, lt_of_le_of_ne modnonneg modlt.symm⟩,
      convert H.mem_op hg (H.mem_inv this),
      rw [←int.group.op_def, ←group.assoc', mul_inv, mul_one] },
    rw int.mul_comm,
    exact H.mem_left_mul hmem.left _ },
  -- Show that `H ⊆ bℤ`
  { rintro ⟨m, rfl⟩,
    rw int.mul_comm,
    exact H.mem_left_mul hmem.left _ }
end

-- in mathlib, this is defined directly in the properties of
-- a group (via a monoid) to make definitional equality work better
instance {G : Type*} [group G] : has_pow G ℤ := ⟨λ g z,
  @gpow_rec _ ⟨ᵍ1⟩ ⟨(ᵍ*)⟩ ⟨λ x, xᵍ⁻¹⟩ z g⟩

lemma inv_mul_distrib (x y : G) :
  (x ᵍ* y)ᵍ⁻¹ = yᵍ⁻¹ ᵍ* xᵍ⁻¹ :=
by rw [←mul_left_inj (x ᵍ* y), mul_inv, mul_assoc, ←mul_assoc x y,
        mul_inv, mul_one, mul_inv]
lemma inv_eq_iff {x y : G} :
  xᵍ⁻¹ = y ↔ x = yᵍ⁻¹ :=
begin
  split;
  { rintro rfl,
    rw inv_inv }
end
@[simp] lemma inv_eq_inv_iff {x y : G} :
  xᵍ⁻¹ = yᵍ⁻¹ ↔ x = y :=
by rw [inv_eq_iff, inv_inv]

-- Ouw own theory of integer powers, basically recapitulating integer addition
@[simp] protected lemma gpow_zero {G : Type*} [group G] (g : G) :
  g ^ (0 : ℤ) = ᵍ1 := rfl
@[simp] protected lemma gpow_succ_coe {G : Type*} [group G] (g : G) (z : ℕ) :
  g ^ (z + 1 : ℤ) = g ᵍ* g ^ (z : ℤ)  := rfl
@[simp] protected lemma gpow_one {G : Type*} [group G] (g : G) :
  g ^ (1 : ℤ) = g :=
begin
  convert group.gpow_succ_coe g 0,
  simp only [group.gpow_zero, mul_one, int.coe_nat_zero]
end
@[simp] protected lemma gpow_two {G : Type*} [group G] (g : G) :
  g ^ (2 : ℤ) = g ᵍ* g :=
begin
  convert group.gpow_succ_coe g 1,
  simp only [int.coe_nat_zero, int.coe_nat_succ, group.gpow_one, zero_add]
end
@[simp] protected lemma gpow_succ_coe' {G : Type*} [group G] (g : G) (z : ℕ) :
  g ^ (z + 1 : ℤ) = g ^ (z : ℤ) ᵍ* g :=
begin
  induction z with z hz,
  { simp only [group.gpow_zero, one_mul, int.coe_nat_zero, group.gpow_one, zero_add] },
  { rw [int.coe_nat_succ, group.gpow_succ_coe, ←int.coe_nat_succ, group.gpow_succ_coe,
        int.coe_nat_succ, hz, group.assoc'] }
end
@[simp] protected lemma gpow_neg_coe {G : Type*} [group G] (g : G) (z : ℕ) :
  g ^ (-z : ℤ) = (g ^ (z : ℤ))ᵍ⁻¹ :=
by { cases z, simp only [group.gpow_zero, int.coe_nat_zero, inv_one, neg_zero], refl }
@[simp] protected lemma gpow_neg {G : Type*} [group G] (g : G) (z : ℤ) :
  g ^ -z = (g ^ z)ᵍ⁻¹ :=
begin
  cases z,
  { simp only [int.of_nat_eq_coe, group.gpow_neg_coe]},
  { rw [int.neg_succ_of_nat_eq, neg_neg, ←inv_inv (g ^ _)],
    refl }
end
@[simp] protected lemma gpow_succ {G : Type*} [group G] (g : G) (z : ℤ) :
  g ^ (z + 1) = g ᵍ* g ^ (z : ℤ) :=
begin
  induction z using int.induction_on with z hz z hz,
  { simp only [group.gpow_zero, mul_one, group.gpow_one, zero_add] },
  { rw [group.gpow_succ_coe, ←int.coe_nat_succ, group.gpow_succ_coe, int.coe_nat_succ, hz] },
  { rw [int.sub_add_cancel, int.sub_eq_add_neg, ←int.neg_add, group.gpow_neg, group.gpow_neg,
        ←mul_left_inj gᵍ⁻¹, ←inv_mul_distrib, ←group.gpow_succ_coe', group.assoc', inv_mul,
        one_mul] }
end
protected lemma gpow_succ' {G : Type*} [group G] (g : G) (z : ℤ) :
  g ^ (z + 1) = g ^ (z : ℤ) ᵍ* g :=
begin
  induction z using int.induction_on with z hz z hz,
  { simp only [group.gpow_zero, one_mul, group.gpow_one, zero_add] },
  { rw [group.gpow_succ_coe, ←int.coe_nat_succ, group.gpow_succ_coe, int.coe_nat_succ, hz,
    group.assoc'] },
  { rw [int.sub_add_cancel, int.sub_eq_add_neg, ←int.neg_add, group.gpow_neg, group.gpow_neg,
        ←mul_right_inj gᵍ⁻¹, ←inv_mul_distrib, ←group.gpow_succ_coe, ←group.assoc', mul_inv,
        mul_one] }
end
@[simp] protected lemma gpow_sub_one {G : Type*} [group G] (g : G) (z : ℤ) :
  g ^ (z - 1) = gᵍ⁻¹ ᵍ* g ^ (z : ℤ) :=
begin
  induction z using int.induction_on with z hz z hz,
  { simp },
  { rw [int.add_sub_cancel, group.gpow_succ, group.assoc', inv_mul, one_mul] },
  { rw [←inv_eq_inv_iff, ←group.gpow_neg, sub_sub, neg_sub, sub_neg_eq_add,
        inv_mul_distrib, ←group.gpow_neg, neg_sub, sub_neg_eq_add, inv_inv,
        ←group.gpow_succ', add_right_comm] }
end
protected lemma gpow_sub_one' {G : Type*} [group G] (g : G) (z : ℤ) :
  g ^ (z - 1) = g ^ (z : ℤ) ᵍ* gᵍ⁻¹ :=
by rw [←mul_right_inj g, ←group.assoc', inv_mul, mul_one, ←group.gpow_succ',
       int.sub_add_cancel]
protected lemma gpow_add {G : Type*} [group G] (g : G) (n m : ℤ) :
  g ^ (n + m) = g ^ n ᵍ* g ^ m :=
begin
  induction n using int.induction_on with n IH n IH generalizing m,
  { simp only [group.gpow_zero, one_mul, zero_add] },
  { rw [group.gpow_succ', ←group.assoc', ←group.gpow_succ,
        group.gpow_succ', add_right_comm, group.gpow_succ', group.assoc',
        IH] },
  { rw [group.gpow_sub_one', ←group.assoc', ←group.gpow_sub_one, ←IH,
        ←int.add_sub_assoc, add_comm, add_comm _ m, int.add_sub_assoc] },
end
protected lemma gpow_comm {G : Type*} [group G] (g : G) (n m : ℤ) :
  g ^ n ᵍ* g ^ m = g ^ m ᵍ* g ^ n :=
by rw [←group.gpow_add, ←group.gpow_add, add_comm]

-- The group generated by a single element
def subgroup.gpowers {G : Type*} [group G] (g : G) : subgroup G :=
{ carrier := set.range ((^) g : ℤ → G),
  mem_e := by { use 0, simp },
  mem_op := by { simp only [forall_apply_eq_imp_iff', set.mem_range, exists_imp_distrib],
    intros n m,
    use (n + m),
    exact group.gpow_add _ _ _ },
  mem_inv := by {
    simp only [forall_apply_eq_imp_iff', set.mem_range, exists_imp_distrib],
    intros n,
    use -n,
    exact group.gpow_neg _ _ } }

lemma subgroup.gpowers_mem_iff {G : Type*} [group G] {g x : G} :
  x ∈ subgroup.gpowers g ↔ ∃ (z : ℤ), g ^ z = x := iff.rfl

-- Take `τ ∈ S₃, ⟨τ⟩ = {e, τ⦄
example : (subgroup.gpowers (equiv.swap 0 1 : Sₙ 3)).carrier = {ᵍ1, equiv.swap 0 1} :=
begin
  ext x,
  simp only [set.mem_insert_iff, subgroup.mem_iff, set.mem_singleton_iff, subgroup.gpowers_mem_iff],
  split,
  { rintro ⟨z, rfl⟩,
    induction z using int.induction_on with z IH z IH,
    { simp },
    { cases IH with IH' IH'; -- rely on mathlib lemmas about powers of equiv.swap
      simp [IH', equiv.group.op_def, equiv.group.e_def] },
    { cases IH with IH' IH'; -- rely on mathlib lemmas about inverse of equiv.swap
      simp [IH', equiv.group.op_def, equiv.group.e_def, equiv.group.inv_def] } },
  { rintro (rfl|rfl),
    { use 0,
      simp only [group.gpow_zero] },
    { use 1,
      simp only [group.gpow_one] } }
end

-- in mathlib, defined as `order_of`
-- mathlib convention is to use 0 instead of infinity for junk values
def order {G : Type*} [group G] (g : G)
  -- we defer the proof of finiteness and the algorithm to calculate order
  [decidable (∃ (n : ℕ) (npos : 0 < n), g ^ (n : ℤ) = ᵍ1)]
  [decidable_pred (λ (n : ℕ), ∃ (npos : 0 < n), g ^ (n : ℤ) = ᵍ1)] : ℕ :=
if h : ∃ (n : ℕ) (npos : 0 < n), g ^ (n : ℤ) = ᵍ1 then nat.find h else 0

-- there are a lot of lemmas about `order_of` working properly
-- so we fake the presence of an algorithm by relying on classical math

open_locale classical

-- The order of `τ` is 2
example : order (equiv.swap 0 1 : Sₙ 3) = 2 :=
begin
  have key : (equiv.swap 0 1 : Sₙ 3) ^ (2 : ℤ) = ᵍ1,
  { simp [equiv.group.op_def, equiv.group.e_def] },
  rw [order, dif_pos, nat.find_eq_iff],
  { split,
    { simp [key] },
    { rintro (_|_|n) hn,
      { simp },
      { suffices : ∃ (x : fin 3), (equiv.swap 0 1 : Sₙ 3) x ≠ (ᵍ1 : Sₙ 3) x,
        { simpa [equiv.ext_iff] },
        use 0,
        simp [equiv.group.e_def] },
      { simpa [nat.succ_lt_succ_iff] using hn } } },
  { use 2,
    simp [key] }
end

lemma swap_mul {α : Type*} [decidable_eq α] ⦃x y z : α⦄
  (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
  equiv.swap x y * equiv.swap y z = equiv.swap x z * equiv.swap x y :=
begin
  ext w,
  by_cases hx : w = x,
  { simpa [hx, equiv.swap_apply_of_ne_of_ne, hxy, hxy.symm, hyz.symm, hzx, hzx.symm] using
    (equiv.swap_apply_of_ne_of_ne hxy.symm hyz).symm },
  by_cases hy : w = y,
  { simp [hx, hy, equiv.swap_apply_of_ne_of_ne, hxy, hxy.symm, hyz.symm, hzx, hzx.symm] },
  by_cases hz : w = z,
  { simp [hx, hy, hz, equiv.swap_apply_of_ne_of_ne, hxy, hxy.symm, hyz.symm, hzx, hzx.symm] },
  { simp [hx, hy, hz, equiv.swap_apply_of_ne_of_ne, hxy, hxy.symm, hyz.symm, hzx, hzx.symm] }
end

-- The order of `σ` is 2
-- TODO: use cycle notation
example : order (equiv.swap 0 1 * equiv.swap 1 2 : Sₙ 3) = 3 :=
begin
  have key : (equiv.swap 0 1 * equiv.swap 1 2 : Sₙ 3) ^ (3 : ℤ) = ᵍ1,
  { ext i,
    fin_cases i;
    norm_num [bit1, equiv.group.e_def] },
  rw [order, dif_pos, nat.find_eq_iff],
  { split,
    { use zero_lt_three,
      exact key },
    { rintro (_|_|_|n) hn,
      { simp },
      { suffices : ∃ (x : fin 3), (equiv.swap 0 1 * equiv.swap 1 2 : Sₙ 3) x ≠ (ᵍ1 : Sₙ 3) x,
        { simpa [equiv.ext_iff] },
        use 0,
        norm_num [equiv.group.e_def] },
      { suffices : ∃ (x : fin 3),
          ((equiv.swap 0 1 * equiv.swap 1 2 : Sₙ 3) ^ (2 : ℤ)) x ≠ (ᵍ1 : Sₙ 3) x,
        { simpa [equiv.ext_iff] },
        use 0,
        norm_num [equiv.group.e_def] },
      { simpa [nat.succ_lt_succ_iff] using hn } } },
  { use 3,
    simp [key] }
end

end group

end e222
