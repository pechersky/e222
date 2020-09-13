import data.fin
import data.matrix.notation
import tactic.ring_exp

open_locale big_operators

variables {n : ℕ} {R : Type*} [field R]

variables {A : matrix (fin (n + 2)) (fin (n + 2)) R}

-- example : (∑ x, ∑ y, A 0 x * (-1) ^ (x : ℕ) * A 1 (x.succ_above y) * (-1) ^ (y : ℕ)) =
--           -(∑ x, ∑ y, A 1 x * (-1) ^ (x : ℕ) * A 0 (x.succ_above y) * (-1) ^ (y : ℕ)) :=
-- begin
--   simp_rw ←finset.sum_neg_distrib,
--   ring_exp,
--   rw fin.sum_univ_cast_succ,
--   rw @fin.sum_univ_cast_succ _ _ (n + 1),
--   congr,
--   ext x,
--   congr' 1 with y,
--   simp,
--   swap,
--   ext y,
--   simp,
-- end


lemma inv_ite {α : Type*} (P : Prop) [decidable P] (f : α → α) (hinv : function.involutive f) (x : α) :
  ite P x (f x) = f (ite (¬ P) (x) (f x)) :=
begin
  rw apply_ite f,
  by_cases h : P,
  { rw [if_pos h, if_neg (not_not.mpr h), hinv x] },
  { rw [if_pos h, if_neg h] },
end

example (k : R) (x y : ℕ) (hne : x ≠ y) : ite (y < x) (k : R) (-k) = - ite (x < y) k (-k) :=
begin
  rw inv_ite _ _ neg_involutive,
  rcases (lt_trichotomy x y) with h|h|h,
  { rw [if_pos h, if_pos],
    exact (not_lt_of_lt h) },
  { exact absurd h hne },
  { rw [if_neg (not_lt_of_lt h), if_neg],
    exact (not_not.mpr h) }
end

lemma test (k : R) (x y : ℕ) (hne : x ≠ y) : ite (y < x) (k : R) (-k) = - ite (x < y) k (-k) :=
begin
  rw inv_ite _ _ neg_involutive,
  rcases (lt_trichotomy x y) with h|h|h,
  { rw [if_pos h, if_pos],
    exact (not_lt_of_lt h) },
  { exact absurd h hne },
  { rw [if_neg (not_lt_of_lt h), if_neg],
    exact (not_not.mpr h) }
end

example (x : fin (n + 1)) (y : fin n) : (-1 : R) ^ (x : ℕ) * (-1) ^ ((x.succ_above y) : ℕ)
  = (-1) ^ ((x + y) : ℕ) * ite ((y : ℕ) < x) 1 (-1) :=
begin
  unfold fin.succ_above,
  rw apply_ite coe,
  convert test ((-1 : R) ^ ((x + y) : ℕ)) x (x.succ_above y) (fin.vne_of_ne (fin.succ_above_ne x y).symm),
  simp [pow_add, fin.succ_above],
end

example : (∑ x : fin (n + 2), ∑ y : fin (n + 1), A 0 (x.succ_above y)) = ∑ x, ∑ y, ite (x ≠ y) (A 0 y) 0 :=
begin
  congr' 1 with x,
end
