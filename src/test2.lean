import data.matrix.notation
import data.nat.basic

universe u
variables {R : Type*} [field R]
variables {n : ℕ}

variables (A : matrix (fin n) (fin n) R)

open_locale matrix big_operators
open matrix

def det' {R : Type*} [field R] :
    Π {n : ℕ}, matrix (fin n) (fin n) R -> fin n -> R
| 0 _ _ := 1
| 1 M i := M i i
| (n + 2) M ⟨0, h⟩ := ∑ j, (M 0 j * (-1 : R) ^ (j.val) * det' (minor M (fin.succ_above ⟨0, h⟩) (fin.succ_above j)) 0)
| (n + 2) M ⟨k + 1, hk⟩ := ∑ j, (M ⟨k + 1, hk⟩ j * (-1 : R) ^ (k + 1 + j.val) * det' (minor M (fin.succ_above ⟨k + 1, hk⟩) (fin.succ_above j))
      ⟨k, (add_lt_add_iff_right 1).mp hk⟩)

@[simp] lemma det_zero_eq_one (A : matrix (fin 0) (fin 0) R) {i} : det' A i = 1 := rfl

@[simp] lemma det_one_eq_elem (A : matrix (fin 1) (fin 1) R) {i} : det' A i = A i i := rfl

@[simp] lemma det_laplace_zero (A : matrix (fin (n + 2)) (fin (n + 2)) R) {h : 0 < n + 2} :
  det' A 0 = ∑ j, (A 0 j * (-1 : R) ^ (j.val) * det' (minor A (fin.succ_above ⟨0, h⟩) (fin.succ_above j)) 0) := rfl

@[simp] lemma det_laplace_nonzero (A : matrix (fin (n + 2)) (fin (n + 2)) R) {i} (h : i + 1 < n + 2) :
  det' A ⟨i + 1, h⟩ = ∑ j, (A ⟨i + 1, h⟩ j * (-1 : R) ^ (i + 1 + j.val) * det' (minor A (fin.succ_above ⟨i + 1, h⟩) (fin.succ_above j))
      ⟨i, (add_lt_add_iff_right 1).mp h⟩) := rfl

@[simp] lemma det_laplace_nonzero' (A : matrix (fin (n + 2)) (fin (n + 2)) R) {i : fin (n + 1)}  :
  det' A i.succ = ∑ j, (A i.succ j * (-1 : R) ^ (i.val + 1 + j.val) * det' (minor A (fin.succ_above i.succ) (fin.succ_above j)) i) :=
begin
  cases i with i h,
  rw <-add_lt_add_iff_right 1 at h,
  exact det_laplace_nonzero A h,
end
#print prefix det'
lemma det_eq_det {i j} (h : i ≠ j) : det' A i = det' A j :=
begin
  induction n with n hn,
  { exact fin.elim0 i },
  cases n,
  { rw subsingleton.elim i j },
  refine fin.cases _ _ i,
  refine fin.cases _ _ j,
  { simp },
  { intros ii,
    simp,
    congr,
    ext jj,
    refine fin.cases _ _ ii,
    simp [hn],
    have h' := hn (A.minor (fin.succ_above 0) jj.succ_above),
    },


end

variables (a b c d : R)

-- this seems to work
#reduce det' ![![a, b], ![c, d]] 0
-- field.add (field.mul (field.mul a field.one) d)
-- (field.add (field.mul (field.mul b (field.mul (field.neg field.one) field.one)) c) field.zero)

example {R : Type*} [field R] {a b c d : R} {n' : ℕ} : det' ![![a, b], ![c, d]] 0 = a * d - b * c :=
begin
  dunfold det',
  have : ∀ f : fin 2 → R, ∑ x : fin 2, f x = f 0 + f 1, by
    { intro f,
      calc ∑ x : fin 2, f x = _ + _ : rfl
      ...                   = f 0 + f 1 : by { simp, ring } },
  rw this,
  simpa,
end

variables {e f g h i: R}

#reduce det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0

#print det'

@[simp] lemma bit0_val {n : ℕ} : ∀ k : fin n, (bit0 k).val = bit0 (k.val) % n
| ⟨_, _⟩ := rfl

@[simp] lemma bit1_val {n : ℕ} (k : fin (n + 1)) : (bit1 k).val = (bit1 (k.val)) % (n + 1) :=
by simp [bit1, bit0, fin.add_def, fin.one_val]

example {R : Type*} [field R] {a b c d e f g h i : R} {n' : ℕ} :
  det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0 =
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
  dunfold det',
  have f3 : ∀ f : fin 3 → R, ∑ x : fin 3, f x = f 0 + f 1 + f 2, by
    { intro f,
      calc ∑ x : fin 3, f x = _ + _: rfl
      ...                   = f 0 + f 1 + f 2: by { simp, ring } },
  rw f3,
  have f2 : ∀ f : fin 2 → R, ∑ x : fin 2, f x = f 0 + f 1, by
    { intro f,
      calc ∑ x : fin 2, f x = _ + _ : rfl
      ...                   = f 0 + f 1 : by { simp, ring } },
  simp only [f2],
  have l00 : (0 : fin 2).succ_above (0 : fin 1) = 1 := rfl,
  have l00' : (0 : fin 3).succ_above (0 : fin 2) = 1 := rfl,
  have l10' : (1 : fin 2).succ_above (0 : fin 1) = 0 := rfl,
  have l10 : (1 : fin 3).succ_above (0 : fin 2) = 0 := rfl,
  have l11 : (1 : fin 3).succ_above (1 : fin 2) = 2 := rfl,
  have l20 : (2 : fin 3).succ_above (0 : fin 2) = 0 := rfl,
  have l21 : (2 : fin 3).succ_above (1 : fin 2) = 1 := rfl,
  have l01' : (0 : fin 3).succ_above (1 : fin 2) = 2 := rfl,
  have l0 : ((⟨0, by norm_num⟩) : fin 2).succ_above (0 : fin 1) = 1 := rfl,
  have l0' : ((⟨0, by norm_num⟩) : fin 3).succ_above (0 : fin 2) = 1 := rfl,
  have l1' : ((⟨0, by norm_num⟩) : fin 3).succ_above (1 : fin 2) = 2 := rfl,
  have hv : ∀ k l m : R, ![k, l, m] 2 = m := by { intros, simpa },
  have hc : ∀ k : R, (λ (i : fin 1), k) = ![k] := by { intros, ext, simp },
  dsimp [minor],
  simp,
  simp [l00, l00', l01', l0, l0', l1', l10, l11, l20, l21, l10', hv, hc],
  ring
end

example {R : Type*} [field R] {a b c d e f g h i: R} {n' : ℕ} :
  det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0 =
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
calc det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0 = _ : rfl
... = a * 1 * (e * 1 * i + (f * (- 1 * 1) * h + 0)) +
  (b * (- 1 * 1) * (d * 1 * i + (f * (- 1 * 1) * g + 0)) +
     (c * (- 1 * (- 1 * 1)) * (d * 1 * h + (e * (- 1 * 1) * g + 0)) + 0)) : rfl
... = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g : by { simp, ring }

-- import data.fintype.card
-- import data.matrix.basic

-- open_locale big_operators

-- namespace matrix

-- universe u
-- variables {α : Type u}

-- open_locale matrix

-- section matrix_notation
-- variables {ι : Type} [fintype ι] [decidable_eq ι]

-- /-- `![]` is the vector with no entries. -/
-- def vec_empty : fin 0 × ι → α
-- | ⟨k, _⟩ := @fin_zero_elim (λ _, α) k

-- /-- `vec_cons h t` prepends an entry `h` to a vector `t`.

-- The inverse functions are `vec_head` and `vec_tail`.
-- The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-- -/
-- def vec_cons {n : ℕ} (h : ι → α) (t : fin n × ι → α) : fin n.succ × ι → α
-- | ⟨⟨0, _⟩, i⟩ := h i
-- | ⟨⟨nat.succ k, hk⟩, i⟩ := t (⟨k, nat.lt_of_succ_lt_succ hk⟩, i)

-- notation `![` l:(foldr `, ` (h t, vec_cons h t) vec_empty `]`) := l

-- /-- `vec_head v` gives the first entry of the vector `v` -/
-- def vec_head {n : ℕ} (v : fin n.succ × ι → α) : ι -> α
-- | i := v (⟨0, nat.succ_pos'⟩, i)

-- /-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
-- def vec_tail {n : ℕ} (v : fin n.succ × ι → α) : fin n × ι → α
-- | ⟨⟨k, hk⟩, i⟩ := v ⟨⟨nat.succ k, nat.succ_lt_succ hk⟩, i⟩

-- end matrix_notation

-- variables {n : ℕ} {n' : Type} [fintype n'] [decidable_eq n']
-- variables {ι : Type} [fintype ι] [decidable_eq ι]

-- section val

-- @[simp] lemma cons_val_succ (x : ι -> α) (u : fin n × ι → α) (i : fin n) (ix : ι) :
--   (vec_cons x u) (i.succ, ix) = u (i, ix) :=
-- by { cases i, refl }

-- @[simp] lemma tail_cons' (u : fin (n + 1) × ι → α) (k : fin n) (ix : ι) :
--   vec_tail u (k, ix) = u (k.succ, ix) :=
-- -- by { ext i, simp [vec_tail], cases i, cases i_fst, { simp [fin.cases], }, rw cons_val_succ'',  }
-- by { cases k, refl }

-- end val

-- section dot_product

-- /-- A product over the `univ` of a pair type equals to
-- the double product over the `univ`s of the `fst` and `snd` types. -/
-- @[to_additive "A sum over the `univ` of a pair type equals to
-- the double sum over the `univ`s of the `fst` and `snd` types."]
-- lemma fintype.prod_product_fintype {α : Type*} {β : Type*} {M : Type*} [fintype α] [comm_monoid M] [fintype β] {f : α × β → M} :
--   ∏ (x : α × β), f x = ∏ x : α, ∏ y : β, f (x, y) :=
-- by { rw <-finset.prod_product, refl }

-- variables [add_comm_monoid α] [has_mul α]

-- @[simp] lemma cons_dot_product (x : ι -> α) (v : fin n × ι → α) (w : fin n.succ × ι → α) :
--   dot_product (vec_cons x v) w = dot_product x (vec_head w) + dot_product v (vec_tail w) :=
-- begin
--   dsimp only [dot_product, vec_head, vec_tail],
--   rw [fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
--       fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
--       <-finset.sum_add_distrib],
--   refine congr_arg finset.univ.sum _,
--   ext i,
--   simpa [fin.sum_univ_succ],
-- end

-- @[simp] lemma dot_product_cons (v : fin n.succ × ι → α) (x : ι -> α) (w : fin n × ι → α) :
--   dot_product v (vec_cons x w) = dot_product (vec_head v) x + dot_product (vec_tail v) w :=
-- begin
--   dsimp only [dot_product, vec_head, vec_tail],
--   rw [fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
--       fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
--       <-finset.sum_add_distrib],
--   refine congr_arg finset.univ.sum _,
--   ext i,
--   simpa [fin.sum_univ_succ],
-- end

-- end dot_product

-- end matrix
