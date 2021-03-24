import data.matrix.notation
import linear_algebra.matrix
import tactic.norm_fin
import tactic.noncomm_ring
import tactic.field_simp
import data.nat.parity

open_locale big_operators

-- 1.1.7
-- Find a formula for `![![1, 1, 1], ![0, 1, 1], ![0, 0, 1]]^n` and prove it by induction
example (n : ℕ) :
  (![![1, 1, 1], ![0, 1, 1], ![0, 0, 1]] ^ n : matrix _ _ ℕ) =
  ![![1, n, (n * (n + 1)) / 2], ![0, 1, n], ![0, 0, 1]] :=
begin
  induction n with n hn,
  { simp only [pow_two, nat.nat_zero_eq_zero, mul_zero, pow_zero],
    ext i j,
    fin_cases i;
    fin_cases j;
    norm_num [matrix.one_apply] },
  { suffices : n * (n + 1) / 2 + (n + 1) = (n + 1) * ((n + 1) + 1) / 2,
      { rw [pow_succ, hn],
        ext i j,
        fin_cases i;
        fin_cases j;
        norm_num [this] },
     apply nat.mul_left_injective (show 0 < 2, by norm_num),
     dsimp,
     rw [nat.div_mul_cancel (nat.even_mul_succ_self _), add_mul,
         nat.div_mul_cancel (nat.even_mul_succ_self _)],
     ring }
end

-- 1.1.16
-- A square matrix `A` is called nilpotent if `A^k = 0` for some `k > 0`.
-- Prove that if `A` is nilpotent, then `I + A` is invertible
example {R n : Type*} [comm_ring R] [fintype n] [decidable_eq n] (A : matrix n n R)
  (k : ℕ) (hk : 0 < k) (nilpotent : A ^ k = 0) : is_unit (1 + A) :=
begin
  have hr : ∀ m (x : matrix n n R), 1 - x ^ m = (1 - x) * ∑ i in finset.range m, x ^ i,
    { intros m x,
      induction m with m hm,
      { simp },
      { rw [finset.sum_range_succ, mul_add, ←hm],
        noncomm_ring } },
  have hl : ∀ m (x : matrix n n R), 1 - x ^ m = (∑ i in finset.range m, x ^ i) * (1 - x),
    { intros m x,
      induction m with m hm,
      { simp },
      { rw [finset.sum_range_succ, add_mul, ←hm, mul_sub, ←pow_succ'],
        noncomm_ring } },
  specialize hr k (-A),
  specialize hl k (-A),
  rw [sub_neg_eq_add] at hr hl,
  refine ⟨⟨1 + A, ∑ i in finset.range k, (-A) ^ i, _, _⟩, rfl⟩,
  { simp [-matrix.mul_eq_mul, ←hr, neg_pow A k, nilpotent] },
  { simp [-matrix.mul_eq_mul, ←hl, neg_pow A k, nilpotent] }
end

-- 1.1.17
-- (a) Find infinitely many matrices `B` such that `BA = I₂` when
-- `A = ![![2, 3], ![1, 2], ![2, 5]]`
-- (b) Prove that there is no matrix `C` such that `AC = I₃`
example (A : matrix (fin 3) (fin 2) ℚ) (hA : A = ![![2, 3], ![1, 2], ![2, 5]]) :
  (∃ (B : matrix (fin 2) (fin 3) ℚ) , B.mul A = 1) ∧
  ∀ (C : matrix (fin 2) (fin 3) ℚ), A.mul C ≠ 1 :=
begin
  split,
  { have c : ℚ := arbitrary _,
    set b : ℚ := - 4 * c - 3 with hb,
    set a : ℚ := - (2 * b + 5 * c) / 3 with ha,
    have d : ℚ := arbitrary _,
    set f : ℚ := d + 1 with hf,
    set e : ℚ := - 2 * (d + f) with he,
    set B : matrix (fin 2) (fin 3) ℚ := ![![a, b, c], ![d, e, f]] with hB,
    use B,
    rw [hA],
    ext i j,
    fin_cases i;
    fin_cases j;
    simp [ha, hb, he, hf];
    ring },
  { intros C H,
    set a : ℚ := C 0 0 with ha,
    set b : ℚ := C 0 1 with hb,
    set c : ℚ := C 0 2 with hc,
    set d : ℚ := C 1 0 with hd,
    set e : ℚ := C 1 1 with he,
    set f : ℚ := C 1 2 with hf,
    have : C = ![![a, b, c], ![d, e, f]],
      { rw [ha, hb, hc, hd, he, hf],
        ext i j,
        fin_cases i;
        fin_cases j;
        refl },
    rw [hA, this] at H,
    have h22 := congr_fun (congr_fun H 2) 2,
    replace h22 : 2 * c + 5 * f = 1,
      { norm_num at h22, exact h22 },
    have h02 := congr_fun (congr_fun H 0) 2,
    have h12 := congr_fun (congr_fun H 1) 2,
    norm_num [matrix.one_apply] at h02 h12,
    replace h12 : c = - (2 * f) := add_eq_zero_iff_eq_neg.mp h12,
    replace h02 : f = 0,
      { rw h12 at h02,
        norm_num at h02,
        ring_nf at h02,
        simpa using h02 },
    replace h12 : c = 0 := by simpa [h02] using h12,
    norm_num [h02, h12] at h22 }
end
