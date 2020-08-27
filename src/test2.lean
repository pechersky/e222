import laplace

open_locale big_operators

universe u
variables {R : Type*} [field R]
variables {n m : ℕ}

variables (A : matrix (fin n) (fin n) R)

open matrix

variables (a b c d : R)
variables (e f g h i: R)

section detreduce

local notation a `+` b := field.add a b
local notation a `*` b := field.mul a b
local notation `-` a := field.neg a
local notation 0 := field.zero
local notation 1 := field.one
-- this seems to work
#reduce det' ![![a, b], ![c, d]] 0
-- field.add (field.mul (field.mul a field.one) d)
-- (field.add (field.mul (field.mul b (field.mul (field.neg field.one) field.one)) c) field.zero)

#reduce det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0

end detreduce

example {R : Type*} [field R] {a b c d : R} {n' : ℕ} : det' ![![a, b], ![c, d]] 0 = a * d - b * c :=
begin
  have : ∀ f : fin 2 → R, ∑ x : fin 2, f x = f 0 + f 1, by
    { intro f,
      calc ∑ x : fin 2, f x = _ + _ : rfl
      ...                   = f 0 + f 1 : by { simp, ring } },
  simpa [this],
end

#print det'


example (z) :
  det' ![![a, b, c], ![d, e, f], ![g, h, i]] z =
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
  have f3 : ∀ f : fin 3 → R, ∑ x : fin 3, f x = f 0 + f 1 + f 2, by
    { intro f,
      calc ∑ x : fin 3, f x = _ + _: rfl
      ...                   = f 0 + f 1 + f 2: by { simp, rw add_assoc (f 0), ring } },
  have f2 : ∀ f : fin 2 → R, ∑ x : fin 2, f x = f 0 + f 1, by
    { intro f,
      calc ∑ x : fin 2, f x = _ + _ : rfl
      ...                   = f 0 + f 1 : by { simp, ring } },
  have l2 : (2 : fin 3).succ_above 0 = 0 := rfl,
  have l2' : (2 : fin 3).succ_above 1 = 1 := rfl,
  have l2'' : (2 : fin 3).succ_above (fin.succ 0) = 1 := rfl,
  have hv : ∀ k l m : R, ![k, l, m] 2 = m := by { intros, simpa },
  have hc : ∀ k : R, (λ (i : fin 1), k) = ![k] := by { intros, ext, simp },
  rcases z with _|_|_,
  { dunfold det',
    norm_num [f3, f2, minor, l2, l2', l2'', hv, hc],
    ring },
  { dunfold det',
    norm_num [f3, f2, minor, l2, l2', l2'', hv, hc],
    ring },
  { dunfold det',
    have l0 : (0 : fin 1).succ.succ.succ_above (fin.succ 0) = 1 := rfl,
    norm_num [f3, f2, minor, l2, l2', l2'', l0, hv, hc],
    ring },
end

example :
  det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0 =
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
  have f3 : ∀ f : fin 3 → R, ∑ x : fin 3, f x = f 0 + f 1 + f 2, by
    { intro f,
      calc ∑ x : fin 3, f x = _ + _: rfl
      ...                   = f 0 + f 1 + f 2: by { simp, rw add_assoc (f 0), ring } },
  have f2 : ∀ f : fin 2 → R, ∑ x : fin 2, f x = f 0 + f 1, by
    { intro f,
      calc ∑ x : fin 2, f x = _ + _ : rfl
      ...                   = f 0 + f 1 : by { simp, ring } },
  have l2 : (2 : fin 3).succ_above 0 = 0 := rfl,
  have l2' : (2 : fin 3).succ_above 1 = 1 := rfl,
  have l2'' : (2 : fin 3).succ_above (fin.succ 0) = 1 := rfl,
  have hv : ∀ k l m : R, ![k, l, m] 2 = m := by { intros, simpa },
  have hc : ∀ k : R, (λ (i : fin 1), k) = ![k] := by { intros, ext, simp },
  simp [f3, f2, minor, l2, l2', l2'', hv, hc],
  norm_num,
  ring,
end

example :
  det' ![![a, b, c], ![d, e, f], ![g, h, i]] 1 =
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
  have f3 : ∀ f : fin 3 → R, ∑ x : fin 3, f x = f 0 + f 1 + f 2, by
    { intro f,
      calc ∑ x : fin 3, f x = _ + _: rfl
      ...                   = f 0 + f 1 + f 2: by { simp, rw add_assoc (f 0), ring } },
  have f2 : ∀ f : fin 2 → R, ∑ x : fin 2, f x = f 0 + f 1, by
    { intro f,
      calc ∑ x : fin 2, f x = _ + _ : rfl
      ...                   = f 0 + f 1 : by { simp, ring } },
  have l2 : (2 : fin 3).succ_above 0 = 0 := rfl,
  have l2' : (2 : fin 3).succ_above 1 = 1 := rfl,
  have l2'' : (2 : fin 3).succ_above (fin.succ 0) = 1 := rfl,
  have c1 : (1 : fin 3) = (0 : fin 2).succ := rfl,
  have hv : ∀ k l m : R, ![k, l, m] 2 = m := by { intros, simpa },
  have hc : ∀ k : R, (λ (i : fin 1), k) = ![k] := by { intros, ext, simp },
  rw (show (1 : fin 3) = (0 : fin 2).succ, by refl),
  simp [f3, f2, minor, l2, l2', l2'', hv, hc],
  norm_num,
  ring,
end

example :
  det' ![![a, b, c], ![d, e, f], ![g, h, i]] 2 =
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
  have f3 : ∀ f : fin 3 → R, ∑ x : fin 3, f x = f 0 + f 1 + f 2, by
    { intro f,
      calc ∑ x : fin 3, f x = _ + _: rfl
      ...                   = f 0 + f 1 + f 2: by { simp, rw add_assoc (f 0), ring } },
  have f2 : ∀ f : fin 2 → R, ∑ x : fin 2, f x = f 0 + f 1, by
    { intro f,
      calc ∑ x : fin 2, f x = _ + _ : rfl
      ...                   = f 0 + f 1 : by { simp, ring } },
  have l2 : (2 : fin 3).succ_above 0 = 0 := rfl,
  have l2' : (2 : fin 3).succ_above 1 = 1 := rfl,
  have l0 : (0 : fin 1).succ.succ.succ_above (fin.succ 0) = 1 := rfl,
  have l2'' : (2 : fin 3).succ_above (fin.succ 0) = 1 := rfl,
  have hv : ∀ k l m : R, ![k, l, m] 2 = m := by { intros, simpa },
  have hc : ∀ k : R, (λ (i : fin 1), k) = ![k] := by { intros, ext, simp },
  rw (show (2 : fin 3) = (1 : fin 2).succ, by refl),
  rw (show (1 : fin 2) = (0 : fin 1).succ, by refl),
  simp [f3, f2, minor, l0, l2, l2', l2'', hv, hc],
  norm_num,
  ring
end

example {R : Type*} [field R] {a b c d e f g h i: R} {n' : ℕ} :
  det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0 =
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
calc det' ![![a, b, c], ![d, e, f], ![g, h, i]] 0 = _ : rfl
... = a * _ * (e * _ * _ + (f * _ * _ + _)) +
  (b * _ * (d * _ * _ + (f * _ * _ + _)) +
     (c * _ * (d * _ * _ + (e * _ * g + _)) + _)) : rfl
... = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g : by { simp, ring }

-- -- import data.fintype.card
-- -- import data.matrix.basic

-- -- open_locale big_operators

-- -- namespace matrix

-- -- universe u
-- -- variables {α : Type u}

-- -- open_locale matrix

-- -- section matrix_notation
-- -- variables {ι : Type} [fintype ι] [decidable_eq ι]

-- -- /-- `![]` is the vector with no entries. -/
-- -- def vec_empty : fin 0 × ι → α
-- -- | ⟨k, _⟩ := @fin_zero_elim (λ _, α) k

-- -- /-- `vec_cons h t` prepends an entry `h` to a vector `t`.

-- -- The inverse functions are `vec_head` and `vec_tail`.
-- -- The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-- -- -/
-- -- def vec_cons {n : ℕ} (h : ι → α) (t : fin n × ι → α) : fin n.succ × ι → α
-- -- | ⟨⟨0, _⟩, i⟩ := h i
-- -- | ⟨⟨nat.succ k, hk⟩, i⟩ := t (⟨k, nat.lt_of_succ_lt_succ hk⟩, i)

-- -- notation `![` l:(foldr `, ` (h t, vec_cons h t) vec_empty `]`) := l

-- -- /-- `vec_head v` gives the first entry of the vector `v` -/
-- -- def vec_head {n : ℕ} (v : fin n.succ × ι → α) : ι -> α
-- -- | i := v (⟨0, nat.succ_pos'⟩, i)

-- -- /-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
-- -- def vec_tail {n : ℕ} (v : fin n.succ × ι → α) : fin n × ι → α
-- -- | ⟨⟨k, hk⟩, i⟩ := v ⟨⟨nat.succ k, nat.succ_lt_succ hk⟩, i⟩

-- -- end matrix_notation

-- -- variables {n : ℕ} {n' : Type} [fintype n'] [decidable_eq n']
-- -- variables {ι : Type} [fintype ι] [decidable_eq ι]

-- -- section val

-- -- @[simp] lemma cons_val_succ (x : ι -> α) (u : fin n × ι → α) (i : fin n) (ix : ι) :
-- --   (vec_cons x u) (i.succ, ix) = u (i, ix) :=
-- -- by { cases i, refl }

-- -- @[simp] lemma tail_cons' (u : fin (n + 1) × ι → α) (k : fin n) (ix : ι) :
-- --   vec_tail u (k, ix) = u (k.succ, ix) :=
-- -- -- by { ext i, simp [vec_tail], cases i, cases i_fst, { simp [fin.cases], }, rw cons_val_succ'',  }
-- -- by { cases k, refl }

-- -- end val

-- -- section dot_product

-- -- /-- A product over the `univ` of a pair type equals to
-- -- the double product over the `univ`s of the `fst` and `snd` types. -/
-- -- @[to_additive "A sum over the `univ` of a pair type equals to
-- -- the double sum over the `univ`s of the `fst` and `snd` types."]
-- -- lemma fintype.prod_product_fintype {α : Type*} {β : Type*} {M : Type*} [fintype α] [comm_monoid M] [fintype β] {f : α × β → M} :
-- --   ∏ (x : α × β), f x = ∏ x : α, ∏ y : β, f (x, y) :=
-- -- by { rw <-finset.prod_product, refl }

-- -- variables [add_comm_monoid α] [has_mul α]

-- -- @[simp] lemma cons_dot_product (x : ι -> α) (v : fin n × ι → α) (w : fin n.succ × ι → α) :
-- --   dot_product (vec_cons x v) w = dot_product x (vec_head w) + dot_product v (vec_tail w) :=
-- -- begin
-- --   dsimp only [dot_product, vec_head, vec_tail],
-- --   rw [fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
-- --       fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
-- --       <-finset.sum_add_distrib],
-- --   refine congr_arg finset.univ.sum _,
-- --   ext i,
-- --   simpa [fin.sum_univ_succ],
-- -- end

-- -- @[simp] lemma dot_product_cons (v : fin n.succ × ι → α) (x : ι -> α) (w : fin n × ι → α) :
-- --   dot_product v (vec_cons x w) = dot_product (vec_head v) x + dot_product (vec_tail v) w :=
-- -- begin
-- --   dsimp only [dot_product, vec_head, vec_tail],
-- --   rw [fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
-- --       fintype.sum_product_fintype, @finset.sum_comm ι _ _ _ _ _ _,
-- --       <-finset.sum_add_distrib],
-- --   refine congr_arg finset.univ.sum _,
-- --   ext i,
-- --   simpa [fin.sum_univ_succ],
-- -- end

-- -- end dot_product

-- -- end matrix
