import linear_algebra.finite_dimensional
import ring_theory.fractional_ideal
import ring_theory.ideal.over
import tactic

open ideal ring

variables {R K : Type*}

variables {S : Type*} [integral_domain R] [integral_domain S] [algebra R S]
variables {L : Type*} [field K] [field L] {f : fraction_map R K}

variables {M : ideal R} [is_maximal M]

lemma trial : is_unit (M : fractional_ideal f) :=
begin
  let setM1 := {x : K | ∀ y ∈ M, f.is_integer (x * f.to_map y)},
  have M1 : fractional_ideal f,
    { use setM1,
      {intros y h,simp,use 0,simp,},
      {intros a b ha hb,intros y h,rw add_mul a b (f.to_map y),
        apply localization_map.is_integer_add,apply ha,exact h,apply hb,exact h,},
      { intros c x h1 y h,
      rw algebra.smul_mul_assoc,
      apply localization_map.is_integer_smul,
      exact h1 y h,},
    },
  have h_nonfrac : ∃ (I : ideal R), (M : fractional_ideal f) * M1 = I,
    { obtain ⟨tR, hR, h⟩ := M1.property,
      sorry,
    },
  obtain ⟨I, hI⟩ := h_nonfrac,
end
