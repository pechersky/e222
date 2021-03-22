import lecture01

namespace e222
open e222.group

variables {G : Type*} [group G]

-- 2.15
example {x y z : G} (h : x * y * z = 1) :
  y * z * x = 1 :=
begin
  suffices : x⁻¹ * x * y * z * x = x⁻¹ * 1 * x,
    { simpa },
  refine congr_arg (λ t, t * x) _,
  rw [←group.mul_assoc, ←group.mul_assoc, group.mul_assoc x],
  exact congr_arg (λ t, x⁻¹ * t) h
end

@[simp] lemma group.mul_left_inj (x : G) {y z : G} :
  x * y = x * z ↔ y = z :=
⟨λ h, by simpa [group.mul_assoc] using congr_arg (λ t, x⁻¹ * t) h, λ h, h ▸ rfl⟩

example {x y z : G} (h : x * y * z = 1) :
  y * x * z = 1 ↔ commute x z :=
begin
  suffices : x⁻¹ * x * y * z * x = x⁻¹ * 1 * x,
    { simp only [group.mul_one, group.inv_mul, group.one_mul] at this,
      rw [←this, ←group.mul_assoc, ←group.mul_assoc, group.mul_left_inj],
      exact iff.rfl },
  refine congr_arg (λ t, t * x) _,
  rw [←group.mul_assoc, ←group.mul_assoc, group.mul_assoc x],
  exact congr_arg (λ t, x⁻¹ * t) h
end

example {S : Type*} : associative (λ (a b : S), a) :=
begin
  intros a b c,
  dsimp,
  refl
end

-- 2.1.7
-- 2.2.1
-- 2.2.15
-- 2.2.20(a)

end e222
