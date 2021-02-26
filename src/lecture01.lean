import data.real.basic
import data.matrix.notation
import linear_algebra.matrix
import linear_algebra.determinant
import group_theory.perm.fin

open_locale big_operators

-- We specialize `matrix` for n × n matrices
notation `Mn[` α `]` n := matrix (fin n) (fin n) α

-- and a shortcut for Mn(ℝ)
notation `MnR ` n := Mn[ℝ]n

variables {n : ℕ}
variables (A : MnR n) (B : MnR n) (C : MnR n)

-- Call the collection of n × n matrices as Mₙ(ℝ).
-- That is a vector space over the real numbers, of dimension n².
example : finite_dimensional.findim ℝ (MnR n) = n ^ 2 :=
by simp [pow_two]   -- rw [matrix.findim_matrix, fintype.card_fin, nat.pow_two]

-- The addition law in the vector space of n × n matrices
example : A + B = λ i j, A i j + B i j :=
by { funext i j, refl } -- matrix.add_val A B

-- Multiplication of a matrix by a real scalar, doesn't work
example (α : ℝ) : α • A = λ i j, α * (A i j) :=
by { funext i j, refl } -- matrix.smul_val α A i j

-- Matrix is a vector space
-- ... noncomputable because it can't provide a basis for us
-- ... since vector_space allows for non-finite spaces
noncomputable example : vector_space ℝ (MnR n) :=
by apply_instance
-- ... so we can use a finite dimensional vector space instance
example : finite_dimensional ℝ (MnR n) :=
by apply_instance

-- An n × n matrix has some finite basis of cardinality n ^ 2
example : ∃ (b : finset (MnR n)),
            (is_basis ℝ (subtype.val : (b : set (MnR n)) → (MnR n)) ∧
            (finset.card b = n ^ 2)) :=
begin
  obtain ⟨s, s_basis⟩ := finite_dimensional.exists_is_basis_finset ℝ (MnR n),
  refine ⟨s, s_basis, _⟩,
  rw [←finite_dimensional.findim_eq_card_finset_basis s_basis,
      matrix.findim_matrix, fintype.card, finset.card_fin, pow_two]
end

variables {m : ℕ}

-- An m × n matrix has some finite basis of cardinality m * n
example : ∃ (b : finset (matrix (fin m) (fin n) ℝ)),
            (is_basis ℝ
              (subtype.val : (b : set (matrix (fin m) (fin n) ℝ)) → (matrix (fin m) (fin n) ℝ)) ∧
            (finset.card b = m * n)) :=
begin
  obtain ⟨s, s_basis⟩ := finite_dimensional.exists_is_basis_finset ℝ (matrix (fin m) (fin n) ℝ),
  refine ⟨s, s_basis, _⟩,
  rw [←finite_dimensional.findim_eq_card_finset_basis s_basis,
      matrix.findim_matrix],
  repeat { rw [fintype.card, finset.card_fin] }
end

-- Multiplication is defined on n x n matrices
example : has_mul (MnR n) := by show_term { apply_instance }

-- Multiplication is defined by sum of row elements times column elements
example : A * B = λ i j, ∑ k , A i k * B k j := rfl

-- An n x n matrix represents a linear operator T : ℝⁿ → ℝⁿ
-- ... vectors in ℝⁿ are represented by functions of (fin n) → ℝ
-- ... linear maps are notated by →ₗ with an optional →ₗ[field R] parameter
example : ∃ (T : (fin n → ℝ) →ₗ fin n → ℝ), T.to_matrix' = A :=
by { use A.to_lin', exact linear_map.to_matrix'_to_lin' _ }

example : (MnR n) ≃ₗ ((fin n → ℝ) →ₗ fin n → ℝ) := matrix.to_lin'

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
  norm_num at h,
  exact h,
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
example (A : MnR 2) {a b c d : ℝ} (hA : A = ![![a, b], ![c, d]]) :
        matrix.det A = a * d - b * c :=
begin
  simp [matrix.det, hA, finset.univ_perm_fin_succ, ←finset.univ_product_univ, finset.sum_product,
        fin.sum_univ_succ, fin.prod_univ_succ],
  ring
end
