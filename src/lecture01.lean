import data.real.basic
import data.matrix.notation
import linear_algebra.matrix
import algebra.invertible

open_locale big_operators

universes u v

/-- We specialize matrix for n × n matrices
with a reducible definition because it's just a shell defn -/
@[reducible] def Mn (α : Type u) (n : ℕ) := matrix (fin n) (fin n) α

/-- and a shortcut for Mn(ℝ) -/
@[reducible] def MnR (n : ℕ) := Mn ℝ n

variables {n : ℕ}
variables (A : MnR n) (B : MnR n) (C : MnR n)

-- Call the collection of n × n matrices as Mₙ(ℝ). 
-- That is a vector space over the real numbers, of dimension n².
example : finite_dimensional.findim ℝ (MnR n) = n ^ 2 :=
  by simp [nat.pow_two] -- rw [matrix.findim_matrix, fintype.card_fin, nat.pow_two]

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
            (is_basis ℝ (subtype.val : (↑b : set (MnR n)) -> (MnR n)) ∧
            (finset.card b = n ^ 2)) :=
begin
  obtain ⟨s, s_basis⟩ := finite_dimensional.exists_is_basis_finset ℝ (MnR n),
  refine ⟨s, s_basis, _⟩,
  rw [<-finite_dimensional.findim_eq_card_finset_basis s_basis,
      matrix.findim_matrix, fintype.card, finset.card_fin, nat.pow_two]
end

variables {m : ℕ} 

-- An m × n matrix has some finite basis of cardinality m * n
example : ∃ (b : finset (matrix (fin m) (fin n) ℝ)),
            (is_basis ℝ (subtype.val : (↑b : set (matrix (fin m) (fin n) ℝ)) -> (matrix (fin m) (fin n) ℝ)) ∧
            (finset.card b = m * n)) :=
begin
  obtain ⟨s, s_basis⟩ := finite_dimensional.exists_is_basis_finset ℝ (matrix (fin m) (fin n) ℝ),
  refine ⟨s, s_basis, _⟩,
  rw [<-finite_dimensional.findim_eq_card_finset_basis s_basis,
      matrix.findim_matrix],
  repeat { rw [fintype.card, finset.card_fin] }
end

-- Multiplication is defined on n x n matrices
#check (by apply_instance : has_mul (MnR n))

-- Multiplication is defined by sum of row elements times column elements
example : A * B = λ i j, ∑ k , A i k * B k j := rfl

-- An n x n matrix represents a linear operator T : ℝⁿ -> ℝⁿ
-- ... vectors in ℝⁿ are represented by functions of (fin n) -> ℝ
-- ... linear maps are notated by →ₗ with an optional →ₗ[field R] parameter
example : ∃ (T : (fin n → ℝ) →ₗ fin n → ℝ), T.to_matrix = A :=
by { use A.to_lin, exact to_lin_to_matrix }

example : MnR n ≃ₗ ((fin n → ℝ) →ₗ fin n → ℝ) := linear_equiv_matrix'.symm

-- Multiplication of matrices is the composition of transformations
example : A * B = (A.to_lin.comp B.to_lin).to_matrix :=
by { rw [<-matrix.mul_to_lin, to_lin_to_matrix], refl }

-- Multiplication of 1 x 1 matrices is commutative
-- ... we provide a coercion definition so we can consider
-- ... a 1 x 1 matrix as if it is a scalar of the underlying field
instance matrix_coe {n : Type u} [fintype n] [unique n] {R : Type v} :
                    has_coe (matrix n n R) R :=
let a := default n in ⟨λ M, M a a⟩

theorem coe_singleton {n : Type u} [fintype n] [unique n] [unique n] {R : Type v}
                      {M : matrix n n R} {a : n} :
                      (↑M : R) = M a a :=
by { rw unique.uniq _ a, refl }

-- Multiplication of 1 x 1 matrices is commutative, the actual statement
example (A : MnR 1) (B : MnR 1) : (A : ℝ) * B = B * A := mul_comm _ _

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
example {i j} : (1 : MnR n) i j = if i = j then 1 else 0 := matrix.one_val

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
example : (A * (B * C)) = ((A.to_lin.comp B.to_lin).comp C.to_lin).to_matrix :=
by { rw [linear_map.comp_assoc, <-matrix.mul_to_lin, <-matrix.mul_to_lin,
        to_lin_to_matrix], refl }