/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

Notation for vectors and matrices
-/

import data.fintype.card
import data.matrix.basic
import tactic.fin_cases
import algebra.big_operators

open_locale big_operators

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : fin 4 → α`.
Nesting vectors gives a matrix, so `![![a, b], ![c, d]] : matrix (fin 2) (fin 2) α`.
This file includes `simp` lemmas for applying operations in
`data.matrix.basic` to values built out of this notation.

## Main definitions

* `vec_empty` is the empty vector (or `0` by `n` matrix) `![]`
* `vec_cons` prepends an entry to a vector, so `![a, b]` is `vec_cons a (vec_cons b vec_empty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

The main new notation is `![a, b]`, which gets expanded to `vec_cons a (vec_cons b vec_empty)`.
-/

namespace matrix

universes u v
variables {α : Type u} {ι : Type}

open_locale matrix

section matrix_notation

/-- `![]` is the vector with no entries. -/
def vec_empty : fin 0 × ι → α
| ⟨k, _⟩ := @fin_zero_elim (λ _, α) k

/-- `vec_cons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vec_head` and `vec_tail`.
The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-/
def vec_cons {n : ℕ} (h : ι → α) (t : fin n × ι → α) : fin n.succ × ι → α
| ⟨⟨0, _⟩, i⟩ := h i
| ⟨⟨nat.succ k, hk⟩, i⟩ := t (⟨k, nat.lt_of_succ_lt_succ hk⟩, i)

notation `![` l:(foldr `, ` (h t, vec_cons h t) vec_empty `]`) := l

/-- `vec_head v` gives the first entry of the vector `v` -/
def vec_head {n : ℕ} (v : fin n.succ × ι → α) : ι -> α
| i := v (⟨0, nat.succ_pos'⟩, i)

/-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
def vec_tail {n : ℕ} (v : fin n.succ × ι → α) : fin n × ι → α
| ⟨⟨k, hk⟩, i⟩ := v ⟨⟨nat.succ k, nat.succ_lt_succ hk⟩, i⟩

end matrix_notation

variables {n : ℕ} {n' : Type} [fintype n']

lemma empty_eq [fintype ι] (v : fin 0 × ι → α) : v = ![] :=
by { ext i, fin_cases i }

section val

@[simp] lemma cons_val_zero (x : ι → α) (u : fin n × ι → α) : (λ i, vec_cons x u (0, i)) = x := rfl

@[simp] lemma cons_val_zero' (h : 0 < n.succ) (x : ι -> α) (u : fin n × ι → α) (ix : ι):
  vec_cons x u (⟨0, h⟩, ix) = x ix :=
rfl

@[simp] lemma cons_val_succ (x : ι -> α) (u : fin n × ι → α) (i : fin n) (ix : ι) :
  (vec_cons x u) (i.succ, ix) = u (i, ix) :=
by { cases i, refl }

@[simp] lemma cons_val_succ' {i : ℕ} (h : i.succ < n.succ) (x : ι -> α) (u : fin n × ι → α) (ix : ι) :
  vec_cons x u (⟨i.succ, h⟩, ix) = u (⟨i, nat.lt_of_succ_lt_succ h⟩, ix) :=
by { rw vec_cons }

@[simp] lemma head_cons (x : ι -> α) (u : fin n × ι → α) :
  vec_head (vec_cons x u) = x :=
by { ext i, simp [vec_head] }

@[simp] lemma head_cons' (x : ι -> α) (u : fin n × ι → α) (ix : ι) :
  vec_head (vec_cons x u) ix = x ix :=
by { simp [vec_head] }

@[simp] lemma tail_cons (x : ι -> α) (u : fin n × ι → α) :
  vec_tail (vec_cons x u) = u :=
-- by { ext i, simp [vec_tail], cases i, cases i_fst, { simp [fin.cases], }, rw cons_val_succ'',  }
by { ext ⟨k, _⟩, cases k, simp [vec_tail] }

@[simp] lemma tail_cons' (u : fin (n + 1) × ι → α) (k : fin n) (ix : ι) :
  vec_tail u (k, ix) = u (k.succ, ix) :=
-- by { ext i, simp [vec_tail], cases i, cases i_fst, { simp [fin.cases], }, rw cons_val_succ'',  }
by { cases k, refl }

@[simp] lemma empty_val' (ix : ι) :
  (λ i, (vec_empty : (fin 0 × ι) → α) (i, ix)) = λ i, fin_zero_elim i :=
by { ext i, refl }

-- @[simp] lemma cons_val' (v : n' × ι → α) (B : matrix (fin n) n' α) (i j) :
--   vec_cons v B i j = vec_cons (v j) (λ i, B i j) i :=
-- by { refine fin.cases _ _ i; simp }

-- @[simp] lemma head_val' (B : matrix (fin n.succ) n' α) (j : n') :
--   vec_head (λ i, B i j) = vec_head B j := rfl

-- @[simp] lemma tail_val' (B : matrix (fin n.succ) n' α) (j : n') :
--   vec_tail (λ i, B i j) = λ i, vec_tail B i j :=
-- by { ext, simp [vec_tail] }

@[simp] lemma cons_head_tail (u : fin n.succ × ι → α) :
 vec_cons (vec_head u) (vec_tail u) = u :=
by { ext ⟨⟨k, _⟩, _⟩, cases k; simp [vec_head, vec_tail] }

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : fin 1 = 0 : fin 1`.
-/
@[simp] lemma cons_val_one (x : ι -> α) (u : fin n.succ × ι → α) (ix : ι) :
  vec_cons x u (1, ix) = vec_head u ix :=
cons_val_succ x u 0 ix

@[simp] lemma cons_val_fin_one (x : ι -> α) (u : fin 0 × ι → α) (i : fin 1) (ix : ι) :
  vec_cons x u (i, ix) = x ix :=
by { fin_cases i, refl }

end val

section dot_product

variables [add_comm_monoid α] [has_mul α]
variables [fintype ι]

@[simp] lemma dot_product_empty (v w : fin 0 × ι → α) :
  dot_product v w = 0 := finset.sum_empty

@[simp] lemma cons_dot_product (x : ι -> α) (v : fin n × ι → α) (w : fin n.succ × ι → α) :
  dot_product (vec_cons x v) w = dot_product x (vec_head w) + dot_product v (vec_tail w) :=
begin
  dsimp only [dot_product, vec_head, vec_tail],
  rw [fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
      fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
      <-finset.sum_add_distrib],
  simpa only [fin.sum_univ_succ, tail_cons', cons_val_succ]
end

@[simp] lemma dot_product_cons (v : fin n.succ × ι → α) (x : ι -> α) (w : fin n × ι → α) :
  dot_product v (vec_cons x w) = dot_product (vec_head v) x + dot_product (vec_tail v) w :=
begin
  dsimp only [dot_product, vec_head, vec_tail],
  rw [fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
      fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
      <-finset.sum_add_distrib],
  simpa only [fin.sum_univ_succ, tail_cons', cons_val_succ]
end

end dot_product

section col_row

@[simp] lemma col_empty [fintype ι] (v : fin 0 × ι → α) : col v = vec_empty :=
empty_eq _

@[simp] lemma col_cons (x : ι -> α) (u : fin n × ι → α) (ix : ι) :
  col (λ k, vec_cons x u (k, ix)) = λ k l, vec_cons x u (k, ix) :=
  -- col (vec_cons x u) = vec_cons (λ _, x) (col u) :=
by { ext i, simp [vec_head, vec_tail] }

@[simp] lemma row_empty [fintype ι] : row (vec_empty : fin 0 × ι → α) = λ _, vec_empty :=
by { ext, refl }

@[simp] lemma row_cons [fintype ι] (x : ι -> α) (u : fin n × ι → α) :
  row (vec_cons x u) = λ _, vec_cons x u :=
by { ext, refl }

end col_row

section transpose
variables {m' : Type} [fintype m'] [fintype ι]

/-- Cast a `matrix` into an uncurried function on `prod` types. -/
definition cast_uncurry (A : matrix m' n' α) : m' × n' -> α :=
λ p, A p.1 p.2

/-- Cast a function on `prod` types into a `matrix`. -/
definition cast_curry (f : m' × n' -> α) : matrix m' n' α :=
λ i j, f (i, j)

local notation `Ç` := cast_uncurry
local notation `ç` := cast_curry

@[simp] lemma cast_mat_uncurry_eq (A : matrix m' n' α) : ∀ p, Ç A p = A p.1 p.2 :=
by simp [cast_uncurry]

@[simp] lemma cast_mat_curry_eq (f : m' × n' -> α) (i j) : ç f i j = f (i, j) := rfl

@[simp] lemma coe_coe_mat_curry_uncurry (A : matrix m' n' α) : ç (Ç A) = A := rfl

@[simp] lemma coe_coe_mat_uncurry_curry (f : m' × n' -> α) : Ç (ç f) = f :=
by { ext i, simp [prod.mk.eta] }

@[simp] lemma transpose_empty_rows (A : matrix m' (fin 0 × ι) α) : Aᵀ = ![] := by { ext i, fin_cases i }

@[simp] lemma transpose_empty_rows' (A : matrix (m' × ι) (fin 0) α) : Ç Aᵀ = ![] := by { ext i, fin_cases i }

@[simp] lemma transpose_empty_cols : (![] : matrix (fin 0 × ι) m' α)ᵀ = λ i, ![] :=
funext (λ i, empty_eq _)

@[simp] lemma transpose_empty_cols' : ((ç ![]) : matrix (fin 0) (m' × ι) α)ᵀ = ç (λ p, ![] (p.2, p.1)) := rfl

@[simp] lemma cons_transpose (v : n' × ι → α) (A : matrix (fin n) (n' × ι) α) :
  (ç (vec_cons v (Ç A)))ᵀ = λ p k, vec_cons v (Ç A) (k, p) :=
by { ext i j, refine fin.cases _ _ j; simp }

@[simp] lemma head_transpose (A : matrix (m' × ι) (fin n.succ) α) : vec_head (Ç Aᵀ) = λ p, A p 0 := rfl

@[simp] lemma tail_transpose (A : matrix (m' × ι) (fin n.succ) α) : vec_tail (Ç Aᵀ) = λ p, A p.2 p.1.succ :=
by { ext ⟨⟩, simp }

end transpose

-- section mul

-- variables [semiring α]
-- variables {m' : Type} [fintype m'] [fintype ι]

-- local notation `Ç` := cast_uncurry
-- local notation `ç` := cast_curry

-- @[simp] lemma empty_mul (A : matrix (fin 0 × ι) n' α) (B : matrix n' m' α) :
--   A ⬝ B = ![] :=
-- empty_eq _

-- @[simp] lemma empty_mul_empty (A : matrix m' (fin 0 × ι) α) (B : matrix (fin 0 × ι) ' α) :
--   A ⬝ B = 0 :=
-- rfl

-- @[simp] lemma mul_empty (A : matrix m' n' α) (B : matrix n' (fin 0 × ι) α) :
--   A ⬝ B = λ _, ![] :=
-- funext (λ _, empty_eq _)

-- lemma mul_val_succ (A : matrix (fin n.succ × ι) n' α) (B : matrix n' m' α) (i : fin n) (j : m') (ix : ι) :
--   (A ⬝ B) (i.succ, ix) j = (vec_tail (Ç (A ⬝ B))) (_) j := by {}

-- @[simp] lemma cons_mul (v : n' → α) (A : matrix (fin n) n' α) (B : matrix n' o' α) :
--   vec_cons v A ⬝ B = vec_cons (vec_mul v B) (A  ⬝ B) :=
-- by { ext i j, refine fin.cases _ _ i, { refl }, simp [mul_val_succ] }

-- end mul

section vec_mul

variables [semiring α]

@[simp] lemma empty_vec_mul (v : fin 0 → α) (B : matrix (fin 0) o' α) :
  vec_mul v B = 0 :=
rfl

@[simp] lemma vec_mul_empty (v : n' → α) (B : matrix n' (fin 0) α) :
  vec_mul v B = ![] :=
empty_eq _

@[simp] lemma cons_vec_mul (x : α) (v : fin n → α) (B : matrix (fin n.succ) o' α) :
  vec_mul (vec_cons x v) B = x • (vec_head B) + vec_mul v (vec_tail B) :=
by { ext i, simp [vec_mul] }

@[simp] lemma vec_mul_cons (v : fin n.succ → α) (w : o' → α) (B : matrix (fin n) o' α) :
  vec_mul v (vec_cons w B) = vec_head v • w + vec_mul (vec_tail v) B :=
by { ext i, simp [vec_mul] }

end vec_mul

-- section mul_vec

-- variables [semiring α]

-- @[simp] lemma empty_mul_vec (A : matrix (fin 0) n' α) (v : n' → α) :
--   mul_vec A v = ![] :=
-- empty_eq _

-- @[simp] lemma mul_vec_empty (A : matrix m' (fin 0) α) (v : fin 0 → α) :
--   mul_vec A v = 0 :=
-- rfl

-- @[simp] lemma cons_mul_vec (v : n' → α) (A : fin n → n' → α) (w : n' → α) :
--   mul_vec (vec_cons v A) w = vec_cons (dot_product v w) (mul_vec A w) :=
-- by { ext i, refine fin.cases _ _ i; simp [mul_vec] }

-- @[simp] lemma mul_vec_cons {α} [comm_semiring α] (A : m' → (fin n.succ) → α) (x : α) (v : fin n → α) :
--   mul_vec A (vec_cons x v) = (x • vec_head ∘ A) + mul_vec (vec_tail ∘ A) v :=
-- by { ext i, simp [mul_vec, mul_comm] }

-- end mul_vec

-- section vec_mul_vec

-- variables [semiring α]

-- @[simp] lemma empty_vec_mul_vec (v : fin 0 → α) (w : n' → α) :
--   vec_mul_vec v w = ![] :=
-- empty_eq _

-- @[simp] lemma vec_mul_vec_empty (v : m' → α) (w : fin 0 → α) :
--   vec_mul_vec v w = λ _, ![] :=
-- funext (λ i, empty_eq _)

-- @[simp] lemma cons_vec_mul_vec (x : α) (v : fin n → α) (w : n' → α) :
--   vec_mul_vec (vec_cons x v) w = vec_cons (x • w) (vec_mul_vec v w) :=
-- by { ext i, refine fin.cases _ _ i; simp [vec_mul_vec] }

-- @[simp] lemma vec_mul_vec_cons (v : m' → α) (x : α) (w : fin n → α) :
--   vec_mul_vec v (vec_cons x w) = λ i, v i • vec_cons x w :=
-- by { ext i j, simp [vec_mul_vec]}

-- end vec_mul_vec

-- section smul

-- variables [semiring α]
-- variables {m' : Type} [fintype m'] [fintype ι]

-- instance scalar_curry : has_scalar (ι -> α) (n' × ι -> α) :=
-- { smul := λ v w p, v p.2 • w p }

-- @[simp] lemma smul_empty (x : ι -> α) (v : fin 0 × ι → α) : x • v = ![] := empty_eq _

-- @[simp] lemma smul_cons (x y : ι -> α) (v : fin n × ι → α) :
--   x • vec_cons y v = vec_cons (x * y) (x • v) :=
-- by { ext i, cases i with k ix, refine fin.cases _ _ k, refl, intros k, simp, }

-- end smul

-- section add

-- variables [has_add α]

-- @[simp] lemma empty_add_empty (v w : fin 0 → α) : v + w = ![] := empty_eq _

-- @[simp] lemma cons_add (x : α) (v : fin n → α) (w : fin n.succ → α) :
--   vec_cons x v + w = vec_cons (x + vec_head w) (v + vec_tail w) :=
-- by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

-- @[simp] lemma add_cons (v : fin n.succ → α) (y : α) (w : fin n → α) :
--   v + vec_cons y w = vec_cons (vec_head v + y) (vec_tail v + w) :=
-- by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

-- end add

-- section zero

-- variables [has_zero α]

-- @[simp] lemma zero_empty : (0 : fin 0 → α) = ![] :=
-- empty_eq _

-- @[simp] lemma cons_zero_zero : vec_cons (0 : α) (0 : fin n → α) = 0 :=
-- by { ext i j, refine fin.cases _ _ i, { refl }, simp }

-- @[simp] lemma head_zero : vec_head (0 : fin n.succ → α) = 0 := rfl

-- @[simp] lemma tail_zero : vec_tail (0 : fin n.succ → α) = 0 := rfl

-- @[simp] lemma cons_eq_zero_iff {v : fin n → α} {x : α} :
--   vec_cons x v = 0 ↔ x = 0 ∧ v = 0 :=
-- ⟨ λ h, ⟨ congr_fun h 0, by { convert congr_arg vec_tail h, simp } ⟩,
--   λ ⟨hx, hv⟩, by simp [hx, hv] ⟩

-- open_locale classical

-- lemma cons_nonzero_iff {v : fin n → α} {x : α} :
--   vec_cons x v ≠ 0 ↔ (x ≠ 0 ∨ v ≠ 0) :=
-- ⟨ λ h, not_and_distrib.mp (h ∘ cons_eq_zero_iff.mpr),
--   λ h, mt cons_eq_zero_iff.mp (not_and_distrib.mpr h) ⟩

-- end zero

-- section neg

-- variables [has_neg α]

-- @[simp] lemma neg_empty (v : fin 0 → α) : -v = ![] := empty_eq _

-- @[simp] lemma neg_cons (x : α) (v : fin n → α) :
--   -(vec_cons x v) = vec_cons (-x) (-v) :=
-- by { ext i, refine fin.cases _ _ i; simp }

-- end neg

-- section minor

-- @[simp] lemma minor_empty (A : matrix m' n' α) (row : fin 0 → m') (col : o' → n') :
--   minor A row col = ![] :=
-- empty_eq _

-- @[simp] lemma minor_cons_row (A : matrix m' n' α) (i : m') (row : fin n → m') (col : o' → n') :
--   minor A (vec_cons i row) col = vec_cons (λ j, A i (col j)) (minor A row col) :=
-- by { ext i j, refine fin.cases _ _ i; simp [minor] }

-- end minor

end matrix

#lint
