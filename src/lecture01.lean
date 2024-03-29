import data.real.basic
import data.matrix.notation
import linear_algebra.matrix
import linear_algebra.determinant
import group_theory.perm.fin
import tactic.norm_swap

open_locale big_operators

namespace e222

section

-- We specialize `matrix` for n × n matrices
notation `Mn[` α `]` n := matrix (fin n) (fin n) α

-- and a shortcut for Mn(ℝ)
notation `MnR ` n := Mn[ℝ]n

variables {n : ℕ}
variables (A : MnR n) (B : MnR n) (C : MnR n)

-- Call the collection of n × n matrices as Mₙ(ℝ).
-- That is a vector space over the real numbers, of dimension n².
example : finite_dimensional.finrank ℝ (MnR n) = n ^ 2 :=
by simp [pow_two]   -- rw [matrix.findim_matrix, fintype.card_fin, nat.pow_two]

-- The addition law in the vector space of n × n matrices
example : A + B = λ i j, A i j + B i j :=
by { funext i j, refl } -- matrix.add_val A B

-- Multiplication of a matrix by a real scalar, doesn't work
example (α : ℝ) : α • A = λ i j, α * (A i j) :=
by { funext i j, refl } -- matrix.smul_val α A i j

-- Matrix is a vector space, which only needs a `module`
example : module ℝ (MnR n) :=
by apply_instance
-- ... so we can use a finite dimensional vector space instance
example : finite_dimensional ℝ (MnR n) :=
by apply_instance

-- An n × n matrix has some finite basis of cardinality n ^ 2
example : ∃ (s : finset (MnR n)) (b : basis s ℝ (MnR n)),
            (finset.card s = n ^ 2) :=
begin
  letI : is_noetherian ℝ (MnR n) := is_noetherian.iff_fg.mpr (by apply_instance),
  let s_basis := is_noetherian.finset_basis ℝ (MnR n),
  refine ⟨_, s_basis, _⟩,
  rw [←finite_dimensional.finrank_eq_card_finset_basis s_basis,
      matrix.finrank_matrix, fintype.card, finset.card_fin, pow_two]
end

variables {m : ℕ}

-- An m × n matrix has some finite basis of cardinality m * n
example : ∃ (s : finset (matrix (fin m) (fin n) ℝ)) (b : basis s ℝ (matrix (fin m) (fin n) ℝ)),
            (finset.card s = m * n) :=
begin
  letI : is_noetherian ℝ (matrix (fin m) (fin n) ℝ) := is_noetherian.iff_fg.mpr (by apply_instance),
  let s_basis := is_noetherian.finset_basis ℝ (matrix (fin m) (fin n) ℝ),
  refine ⟨_, s_basis, _⟩,
  rw [←finite_dimensional.finrank_eq_card_finset_basis s_basis,
      matrix.finrank_matrix],
  repeat { rw [fintype.card, finset.card_fin] }
end

-- Multiplication is defined on n x n matrices
example : has_mul (MnR n) := by apply_instance -- show_term gives matrix.has_mul

-- Multiplication is defined by sum of row elements times column elements
example : A * B = λ i j, ∑ k , A i k * B k j := rfl

-- An n x n matrix represents a linear operator T : ℝⁿ → ℝⁿ
-- ... vectors in ℝⁿ are represented by functions of (fin n) → ℝ
-- ... linear maps are notated by →ₗ with an optional →ₗ[field R] parameter
example : ∃ (T : (fin n → ℝ) →ₗ[ℝ] fin n → ℝ), T.to_matrix' = A :=
by { use A.to_lin', exact linear_map.to_matrix'_to_lin' _ }

example : (MnR n) ≃ₗ[ℝ] ((fin n → ℝ) →ₗ[ℝ] fin n → ℝ) := matrix.to_lin'

-- Multiplication of matrices is the composition of transformations
example : A * B = (A.to_lin'.comp B.to_lin').to_matrix' :=
by rw [←matrix.to_lin'_mul, linear_map.to_matrix'_to_lin', matrix.mul_eq_mul]

-- Multiplication of 1 x 1 matrices is commutative
example (A : MnR 1) (B : MnR 1) : A * B = B * A :=
begin
  ext i j,
  rw [matrix.mul_eq_mul, matrix.mul_eq_mul, matrix.mul_apply, matrix.mul_apply,
      finset.sum_congr rfl],
  intros x _,
  rw mul_comm,
  congr
end

-- Multiplication of 2 x 2 matrices is not necessarily commutative
example : ∃ (A : MnR 2) (B : MnR 2), A * B ≠ B * A :=
begin
  use ![![0, 1], ![0, 0]],
  use ![![0, 0], ![0, 1]],
  intros h,
  replace h := congr_fun (congr_fun h 0) 1,
  norm_num at h
end

-- Zero matrix is the zero element of the vector space,
-- adding it to any element, you get the same
-- ... following examples use the monoid and semiring instances of matrices
example (A : matrix (fin m) (fin n) ℝ) : A + 0 = A := add_zero _
example (A : matrix (fin m) (fin n) ℝ) : 0 + A = A := zero_add _

-- The identity matrix
example {i j} : (1 : MnR n) i j = if i = j then 1 else 0 := matrix.one_apply

-- Multiplication by the identity matrix gets anything back
example : A * 1 = A := mul_one _
example : 1 * A = A := one_mul _

-- Matrix distributive law
example : A * (B + C) = A * B + A * C :=
mul_add _ _ _

-- Matrix associative law
example : A * (B * C) = A * B * C :=
(mul_assoc _ _ _).symm

-- Proving associativity by composition of transformation
example : (A * (B * C)) = ((A.to_lin'.comp B.to_lin').comp C.to_lin').to_matrix' :=
by { rw [linear_map.comp_assoc, ←matrix.to_lin'_mul, ←matrix.to_lin'_mul,
         linear_map.to_matrix'_to_lin'], refl }

-- A 1 x 1 matrix is invertible iff the element is nonzero
example (A : MnR 1) : A ≠ 0 ↔ is_unit A :=
begin
  have nonzero : A ≠ 0 → A 0 0 ≠ 0,
    { intros nonzeroA nz,
      refine nonzeroA _,
      ext i j,
      convert nz },
  split,
  { intros hA,
    refine ⟨⟨A, ![![1 / (A 0 0)]], _, _⟩, rfl⟩;
    { ext i j,
      rw [matrix.mul_eq_mul, matrix.mul_apply, fin.sum_univ_succ, subsingleton.elim i 0,
          subsingleton.elim j 0],
      simp [nonzero hA] } },
  { rintros ⟨⟨A, B, h, h'⟩, rfl⟩ H,
    have : A 0 0 * B 0 0 = 1,
      { convert matrix.ext_iff.mpr h 0 0,
        rw [matrix.mul_eq_mul, matrix.mul_apply, fin.sum_univ_succ, fin.sum_univ_zero, add_zero] },
    have hz : A 0 0 = 0 := matrix.ext_iff.mpr H 0 0,
    rw [hz, zero_mul] at this,
    exact zero_ne_one this }
end

-- A 2 x 2 matrix is invertible if the "determinant" is nonzero, without definition of determinants
example (A : MnR 2) {a b c d} (hA : A = ![![a, b], ![c, d]]) :
        a * d - b * c ≠ 0 ↔ is_unit A :=
begin
  split,
  { intros h,
    refine ⟨⟨A, (1 / (a * d - b * c)) • ![![d, -b], ![-c, a]], _, _⟩, rfl⟩;
    { ext i j,
      fin_cases i;
      fin_cases j;
      field_simp [hA, h];
      ring } },
  { rintros ⟨⟨A, B, hAB, hBA⟩, rfl⟩ H,
    simp only [units.coe_mk] at hA,
    rw [←matrix.ext_iff, hA, matrix.mul_eq_mul] at hBA hAB,
    classical,
    by_cases hn : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0,
    { have ha' : a = b * c / d,
        { rwa [eq_div_iff, ←sub_eq_zero],
          simp [hn] },
      have hBA' : a * B 0 0 + c * B 0 1 = 1,
        { convert hBA 0 0 using 2;
          simp [mul_comm] },
      have hBA'' : b * B 0 0 + d * B 0 1 = 0,
        { convert hBA 0 1 using 2;
          simp [mul_comm] },
      have hBv : B 0 1 = - b / d * B 0 0,
        { field_simp [hn],
          rw ←eq_neg_iff_add_eq_zero at hBA'',
          simp [hBA'', mul_comm] },
      have hd' : d = 0,
        { field_simp [ha', hn, hBv] at hBA',
          rw ←hBA',
          ring },
      simpa [hd'] using hn },
    { simp only [not_and_distrib, not_not, ne.def] at hn,
      have v0 : ∀ x, matrix.vec_cons 0 (λ (i : fin 1), 0) x = 0,
        { intros x,
          fin_cases x;
          refl },
      have h00 := hAB 0 0,
      have h01 := hAB 0 1,
      have h11 := hAB 1 1,
      have h10 := hAB 1 0,
      have h00' := hBA 0 0,
      have h01' := hBA 0 1,
      have h11' := hBA 1 1,
      have h10' := hBA 1 0,
      rcases hn with (rfl | rfl | rfl | rfl);
      { simp only [zero_sub, sub_zero, zero_mul, mul_zero, neg_eq_zero, mul_eq_zero] at H,
        rcases H with (rfl | rfl);
        simp [matrix.mul_apply, fin.sum_univ_succ] at h00 h01 h11 h10 h00' h01' h11' h10';
        assumption } } }
end

-- determinant of a 2 x 2 matrix is a * d - b * c
lemma det_2 (A : MnR 2) {a b c d : ℝ} (hA : A = ![![a, b], ![c, d]]) :
        matrix.det A = a * d - b * c :=
begin
  simp [hA, matrix.det_succ_row_zero, fin.sum_univ_succ],
  ring
end

--  A matrix is invertible iff the determinant is nonzero
lemma is_unit_iff_det_ne_zero  {n : ℕ} (A : MnR n) : is_unit A ↔ A.det ≠ 0 :=
begin
  rw matrix.is_unit_iff_is_unit_det,
  exact is_unit_iff_ne_zero
end

-- The general linear group, as a subtype of matrices
abbreviation GLₙ (n : ℕ) (α : Type*) [comm_ring α] : Type* := units (matrix (fin n) (fin n) α)

lemma GLₙ.is_unit_det {n : ℕ} (A : GLₙ n ℝ) : is_unit (matrix.det (A : MnR n)) :=
begin
  rw ←matrix.is_unit_iff_is_unit_det,
  exact units.is_unit _
end

lemma GLₙ.det_ne_zero {n : ℕ} (A : GLₙ n ℝ) : matrix.det (A : MnR n) ≠ 0 :=
begin
  rw ←is_unit_iff_det_ne_zero,
  exact units.is_unit _
end

-- For GL₁(ℝ) matrices, everything but 0
example (A : GLₙ 1 ℝ) : (A : MnR 1) ≠ 0 :=
begin
  intro H,
  simpa [H] using A.det_ne_zero
end

-- For M₂(ℝ) matrices, there are nonzero examples that are not GL₂(ℝ)
example (A : GLₙ 2 ℝ) : ![![(0 : ℝ), 1], ![0, 0]] ≠ (A : MnR 2) :=
begin
  intro H,
  apply A.det_ne_zero,
  rw [←H, det_2 _ rfl],
  simp
end

-- If the inverse exists, it is unique
example {n : ℕ} (A : MnR n) (h : ∃ B, A * B = 1 ∧ B * A = 1) : ∃! B, (A * B = 1 ∧ B * A = 1) :=
begin
  refine exists_unique_of_exists_of_unique h _,
  rintros B C ⟨hAB, hBA⟩ ⟨hAC, hCA⟩,
  have : B * (A * B) = B * (A * C),
    { rw [hAB, hAC] },
  rwa [matrix.mul_eq_mul, matrix.mul_eq_mul, ←matrix.mul_assoc,
      matrix.mul_eq_mul, matrix.mul_eq_mul, ←matrix.mul_assoc,
      ←matrix.mul_eq_mul, ←matrix.mul_eq_mul, ←matrix.mul_eq_mul, hBA,
      one_mul, one_mul] at this
end

-- GLₙ(ℝ) is not closed under addition
example (n : ℕ) : ¬ is_unit (((1 : GLₙ (n + 1) ℝ) : MnR (n + 1)) + (-1 : GLₙ (n + 1) ℝ)) :=
begin
  rw [units.coe_one, units.coe_neg_one, add_right_neg],
  exact not_is_unit_zero
end

-- GLₙ(ℝ) is not closed under scalar multiplication by 0
example (k : ℝ) {n : ℕ} (A : GLₙ (n + 1) ℝ) : ¬ is_unit (k • (A : MnR (n + 1))) ↔ k = 0 :=
begin
  rw not_iff_comm,
  split,
  { intro h,
    refine ⟨⟨k • (A : MnR (n + 1)), (k • A)⁻¹, _, _⟩, rfl⟩;
    { rw matrix.mul_eq_mul,
      rw matrix.mul_nonsing_inv <|> rw matrix.nonsing_inv_mul,
      rw [matrix.det_smul, is_unit_iff_ne_zero, mul_ne_zero_iff],
      exact ⟨pow_ne_zero _ h, A.det_ne_zero⟩ } },
  { rintro ⟨⟨A', B, hAB, hBA⟩, h⟩ rfl,
    rw [units.coe_mk, zero_smul] at h,
    rw [h, zero_mul] at hAB,
    exact zero_ne_one hAB }
end

-- GLₙ(ℝ) is closed under multiplication, proof 1
example {n : ℕ} (A B : GLₙ n ℝ) : is_unit ((A : MnR n) * B) :=
begin
  refine ⟨⟨(A : MnR n) * B, B⁻¹ * A⁻¹, _, _⟩, rfl⟩;
  simp_rw [matrix.mul_eq_mul],
  { rw [matrix.mul_assoc, ←matrix.mul_assoc (B : MnR n), matrix.mul_nonsing_inv _ B.is_unit_det,
      matrix.one_mul, matrix.mul_nonsing_inv _ A.is_unit_det] },
  { rw [matrix.mul_assoc, ←matrix.mul_assoc _ (A : MnR n), matrix.nonsing_inv_mul _ A.is_unit_det,
      matrix.one_mul, matrix.nonsing_inv_mul _ B.is_unit_det] }
end

-- GLₙ(ℝ) is closed under multiplication, proof 2
example {n : ℕ} (A B : GLₙ n ℝ) : is_unit ((A : MnR n) * B) :=
begin
  rw [matrix.is_unit_iff_is_unit_det, matrix.mul_eq_mul, matrix.det_mul],
  exact A.is_unit_det.mul B.is_unit_det
end

-- GLₙ(ℝ) contains 1
example {n : ℕ} : is_unit (1 : MnR n) := ⟨⟨1, 1, one_mul _, one_mul _⟩, rfl⟩

-- GLₙ(ℝ) contains inverses
example {n : ℕ} (A : GLₙ n ℝ) : is_unit ((A : MnR n)⁻¹) :=
begin
  refine ⟨⟨A⁻¹, A, _, _⟩, rfl⟩,
  rw [matrix.mul_eq_mul, matrix.nonsing_inv_mul _ A.is_unit_det],
  rw [matrix.mul_eq_mul, matrix.mul_nonsing_inv _ A.is_unit_det]
end

-- GLₙ(ℝ) multiplication is associative
example {n : ℕ} (A B C : GLₙ n ℝ) : A * B * C = A * (B * C) :=
begin
  rw mul_assoc -- inherited from group structure on `units`
end

class group (α : Type*) :=
(op : α → α → α)
(infixl `ᵍ*`:70 := op)
(assoc' : ∀ g h k : α, g ᵍ* (h ᵍ* k) = (g ᵍ* h) ᵍ* k)
(e : α)
(notation `ᵍ1`:50 := e)
(op_e' : ∀ g, g ᵍ* ᵍ1 = g)
(e_op' : ∀ g, ᵍ1 ᵍ* g = g)
(inv : α → α)
(postfix `ᵍ⁻¹`:max := inv)
(inv_op' : ∀ g, gᵍ⁻¹ ᵍ* g = e)
(op_inv' : ∀ g, g ᵍ* gᵍ⁻¹ = e)

infixl ` ᵍ* `:70 := group.op
notation `ᵍ1` := group.e
postfix `ᵍ⁻¹`:std.prec.max_plus := group.inv

variables {α : Type*} [group α]

namespace group

lemma mul_assoc (g h k : α) : g ᵍ* (h ᵍ* k) = (g ᵍ* h) ᵍ* k := group.assoc' _ _ _
@[simp] lemma mul_one (g : α) : g ᵍ* ᵍ1 = g := group.op_e' _
@[simp] lemma one_mul (g : α) : ᵍ1 ᵍ* g = g := group.e_op' _
@[simp] lemma inv_mul (g : α) : gᵍ⁻¹ ᵍ* g = ᵍ1 := inv_op' _
@[simp] lemma mul_inv (g : α) : g ᵍ* gᵍ⁻¹ = ᵍ1 := op_inv' _

end group

class abelian_group (α : Type*) extends group α :=
(comm : ∀ (g h : α), g ᵍ* h = h ᵍ* g)

-- The integers are an abelian group
example : abelian_group ℤ :=
{ op := (+),
  assoc' := λ _ _ _, (int.add_assoc _ _ _).symm,
  e := 0,
  op_e' := int.add_zero,
  e_op' := int.zero_add,
  inv := λ x, -x,
  inv_op' := int.add_left_neg,
  op_inv' := int.add_right_neg,
  comm := int.add_comm }

-- Any vector space is an abelian group. Uses the proofs for groups already in mathlib
example (K V : Type*) [field K] [add_comm_group V] [module K V] : abelian_group V :=
{ op := (+),
  assoc' := λ _ _ _, (add_assoc _ _ _).symm,
  e := 0,
  op_e' := add_zero,
  e_op' := zero_add,
  inv := λ x, -x,
  inv_op' := add_left_neg,
  op_inv' := add_right_neg,
  comm := add_comm }

-- The bijections (symmetries) of a type are a group
-- this example has `(f * g)(x) = g(f(x))`
example (T : Type*) : group (T ≃ T) :=
{ op := equiv.trans,
  assoc' := equiv.trans_assoc,
  e := equiv.refl _,
  op_e' := equiv.trans_refl,
  e_op' := equiv.refl_trans,
  inv := equiv.symm,
  inv_op' := equiv.symm_trans_self,
  op_inv' := equiv.self_trans_symm }

end

open matrix set linear_map
variables {R n : Type*} [comm_ring R] [fintype n] [decidable_eq n]

-- The definition of GLₙ(ℝ) is group-equivalent to the mathlib definition
example {n : ℕ} : (GLₙ n ℝ) ≃* linear_map.general_linear_group ℝ (fin n → ℝ) :=
units.map_equiv to_lin_alg_equiv'.to_mul_equiv

-- The symmetric group, as permutations of `fin n`
notation `Sₙ ` n := equiv.perm (fin n)

-- Sₙ is a finite group of order `n!`
example {n : ℕ} : fintype.card (Sₙ n) = nat.factorial n :=
by rw [fintype.card_perm, fintype.card_fin]

-- Sₙ is not abelian for n = 3
example : ∃ g h : Sₙ 3, g * h ≠ h * g :=
begin
  use [equiv.swap 0 1, equiv.swap 0 2],
  intro H,
  -- evaluate the swaps at the first element, which will make 2 = 1
  have := equiv.congr_fun H 0,
  -- norm_num discharges the false goal with the false hypothesis
  norm_num at this
end

end e222
