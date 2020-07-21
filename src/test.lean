-- import data.real.basic
-- import data.matrix.notation
-- import tactic.fin_cases
-- import linear_algebra.basis
-- import linear_algebra.determinant
-- import data.finset

-- universe u
-- variables {α : Type u} [semiring α]
-- variables {m n : ℕ} {m' n' : Type} [fintype m'] [fintype n']

-- @[simp] lemma smul_cons_cons (x : α) (v : n' → α) (A : matrix (fin m) n' α) :
--   x • matrix.vec_cons v A = matrix.vec_cons (x • v) (x • A) :=
-- by { ext i, refine fin.cases _ _ i; simp }

-- @[simp] lemma smul_cons_cons' (x : α) (v : n' → α) (A : ((fin m) × n') -> α) :
--   x • matrix.vec_cons v A = matrix.vec_cons (x • v) (x • A) :=
-- by { ext i, refine fin.cases _ _ i; simp }

-- def vec_cons {n : ℕ} (h : α) (t : (fin n × m') → α) : (fin n.succ × m') → α :=
-- λ ⟨⟨ni, hni⟩, mi⟩, dite (ni < n) (λ hn, t ⟨⟨ni, hn⟩, mi⟩) (λ _, h)

-- #check @vec_cons
-- @[simp] lemma smul_empty' (x : α) : x • @matrix.vec_empty (m' → α) = matrix.vec_empty :=
-- by { ext i, fin_cases i }

-- @[simp] lemma smul_empty'' (x : α) : x • @matrix.vec_empty ((m' × n') → α) = matrix.vec_empty :=
-- by { ext i, fin_cases i }

-- example (x : ℝ) (A B : matrix (fin 1) (fin 1) ℝ) (hx : x = 2)
--         (hA : A = ![![1]]) (hB : B = ![![2]]) :
--         x • A = B :=
-- begin
--   rw [hx, hA, hB],
--   simp,
-- end

-- example (x : ℝ) (A B : matrix (fin 1) (fin 1) ℝ) (hx : x = 2)
--         (hA : A = matrix.vec_cons ![1] (![] : fin 0 -> fin 1 -> ℝ)) (hB : B = ![![2]]) :
--         x • A = B :=
-- begin
--   rw [hx, hA, hB],
--   simp only [mul_one, smul_cons_cons, matrix.smul_cons, matrix.smul_empty],
--   -- ⊢ matrix.vec_cons ![2] (2 • matrix.vec_empty) = ![![2]]
-- end

import data.matrix.notation
import linear_algebra.nonsingular_inverse
import tactic
import data.real.basic
import data.mv_polynomial

section detdef

universe u
variables {R : Type*} [field R]
variables {n : ℕ}

variables (a b c d : R)
variables (A B : matrix (fin n) (fin n) R)

open_locale matrix big_operators
open matrix

def det' {R : Type*} [field R] :
    Π {n : ℕ}, matrix (fin n) (fin n) R -> fin n -> R
| 0 _ _ := 1
| 1 M i := M i i
| (n + 1) M i :=
  match i with
  | ⟨0, _⟩  := ∑ j, (M i j * (-1 : R) ^ (i.val + j.val) * det' (minor M (fin.succ_above i) (fin.succ_above j)) 0)
  | ⟨k + 1, hk⟩ := ∑ j, (M i j * (-1 : R) ^ (i.val + j.val) * det' (minor M (fin.succ_above i) (fin.succ_above j))
      ⟨k, (add_lt_add_iff_right 1).mp hk⟩
      )
  end

#check det' ![![a, b], ![c, d]] 0

#check matrix.adjugate ![![a, b], ![c, d]]

variables (n' m' : Type) [fintype n'] [fintype m'] 

variable {m : ℕ}

@[simp] lemma update_row_empty (M : fin 0 -> fin n -> R) {z : fin 0} {v : fin n -> R} : update_row M z v = ![] := empty_eq _

@[simp] lemma update_row_zero (A : matrix (fin m) n' R) (v w : n' → R) :
  update_row (vec_cons v A) 0 w = vec_cons w A :=
begin
  ext i j,
  refine fin.cases _ _ i,
  { simp },
  { intros,
    simp only [update_row, vec_cons, function.update],
    split_ifs with h,
    { exact absurd h (fin.succ_ne_zero _) },
    { simp only [fin.cons_succ] } }
end

@[simp] lemma update_row_cons (A : matrix (fin m) n' R) (v w : n' -> R) {i : fin m}  :
  update_row (vec_cons v A) i.succ w = vec_cons v (update_row A i w) :=
begin
  ext ii j,
  refine fin.cases _ _ ii,
  { simp [update_row_ne (fin.succ_ne_zero i).symm] },
  { intros,
    simp only [update_row, vec_cons, function.update],
    split_ifs with h;
    simp [h] }
end

@[simp] lemma update_col_empty (M : matrix (fin 0) (fin 0) R) {z : fin 0} {v : fin 0 -> R} :
  update_column M z v = ![] := empty_eq _

@[simp] lemma update_col_column_empty [subsingleton n'] {h : decidable_eq n'} 
  (M : matrix (fin n) n' R) {z : n'} {v : fin n → R} :
  update_column M z v = λ i j, v i :=
begin
  ext i j,
  rw subsingleton_iff.mp (by apply_instance) z j, 
  simp [subsingleton_iff.mp _ z j],
end

@[simp] lemma update_col_cons [decidable_eq m']
  (A : matrix (fin n) m' R) (v : m' → R) (w : fin (n + 1) → R) {j} :
    update_column (vec_cons v A) j w =
      vec_cons (function.update v j (w 0)) (update_column A j (λ i, w i.succ)) :=
begin
  ext i jj,
  simp only [update_column],
  refine fin.cases (by simp) _ i,
  intros,
  simp only [update_row, vec_cons, function.update],
  split_ifs;
  simp [h]
end

example : matrix.adjugate ![![a, b], ![c, d]] = ![![d, -b], ![-c, a]] :=
begin
    simp [matrix.adjugate],
    simp [cramer, cramer_map],
    ext i j,
    refine fin.cases _ _ i,
    refine fin.cases _ _ j,
    simp [cramer_map, det],
end

example {R : Type*} [field R] {z : fin 0} : det' (![] : matrix (fin 0) (fin 0) R) z = 1 := rfl

example {R : Type*} [field R] {a : R} {z : fin 1} {n' : ℕ} : det' ![![a]] z = a :=
begin
  simp [det'],
end

example {R : Type*} [field R] {a b c d : R} : det' ![![a, b], ![c, d]] 0 = a * d - b * c :=
begin
    simp [det'],
    refl,
end

end detdef

section polynomial

universes u v

variables (n : Type u) [fintype n] [decidable_eq n]

noncomputable def det_poly : mv_polynomial (n × n) ℤ :=
matrix.det $ λ i j : n, mv_polynomial.X (i, j)

variables {n} {R : Type v} [comm_ring R] (M : matrix n n R)

namespace mv_polynomial

theorem eval₂_int_cast {α β σ : Type*} [comm_ring α] [comm_ring β]
  (f : α → β) (g : σ → β) [is_ring_hom f] (n : ℤ) :
  (n : mv_polynomial σ α).eval₂ f g = n :=
int.induction_on n (eval₂_zero f g)
  (λ i ih, by rw [int.cast_add, int.cast_add, int.cast_one, int.cast_one, eval₂_add, ih, eval₂_one])
  (λ i ih, by rw [int.cast_sub, int.cast_sub, int.cast_one, int.cast_one, eval₂_sub, ih, eval₂_one])

end mv_polynomial

open mv_polynomial

theorem eval_det_poly : (det_poly n).eval₂ coe (λ p, M p.1 p.2) = M.det :=
begin
  delta det_poly,
  unfold matrix.det,
  haveI : is_semiring_hom (coe : ℤ → R) := ⟨int.cast_zero, int.cast_one, int.cast_add, int.cast_mul⟩,
  haveI : is_ring_hom (coe : ℤ → R) := is_ring_hom.of_semiring _,
  simp_rw [eval₂_sum, eval₂_mul, eval₂_int_cast, eval₂_prod, eval₂_X]
end

end polynomial

example {R : Type*} [field R] {a b c d : R} (A : matrix (fin 2) (fin 2) R) (hA : A = ![![a, b], ![c, d]]) :
  matrix.det A = a * d - b * c :=
begin
  rw [<-eval_det_poly],
  delta det_poly,
  simp [hA],

end