import algebra.order.floor

/-! # IMO 2010 A1 (P1) -/

namespace IMOSL
namespace IMO2010A1

variables {F : Type*} [linear_ordered_field F] [floor_ring F]

/-- For any `r : F` with `1 < r`, we have `⌊r⁻¹⌋ = 0`. -/
lemma inv_floor_eq_zero {r : F} (h : 1 < r) : ⌊r⁻¹⌋ = 0 :=
  int.floor_eq_zero_iff.mpr ⟨inv_nonneg.mpr (zero_lt_one.trans h).le, inv_lt_one h⟩



/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_ring R] [floor_ring R] (f : F → R) :
  (∀ x y : F, f (⌊x⌋ * y) = f x * ⌊f y⌋) ↔ (∃ C : R, ⌊C⌋ = 1 ∧ f = λ _, C) ∨ f = 0 :=
---- `→`
⟨λ h, (mul_right_eq_self₀.mp ((congr_arg f (mul_zero _).symm).trans (h 0 0)).symm).imp
  ---- Case 1: `⌊f(0)⌋ = 1`
  (λ h0, ⟨f 0, int.cast_eq_one.mp h0, funext $ λ x,
    (mul_one _).symm.trans $ h0 ▸ (h x 0).symm.trans $ congr_arg f (mul_zero _)⟩)
  ---- Case 2: `f(0) = 0`
  -- First reduce to `f(1) = 0`
  (λ h0, suffices f 1 = 0,
    from funext $ λ y, let h1 := (h 1 y).trans (mul_eq_zero_of_left this _) in
      suffices (⌊(1 : F)⌋ : F) = 1, from one_mul y ▸ this ▸ h1,
    int.cast_eq_one.mpr int.floor_one,
  -- Now reduce to `⌊f(1/2)⌋ = 0`
  suffices ⌊f 2⁻¹⌋ = 0, 
    from let h1 := (h 2 2⁻¹).trans (mul_eq_zero_of_right _ $ int.cast_eq_zero.mpr this) in
      suffices (⌊(2 : F)⌋ : F) * 2⁻¹ = 1, from this ▸ h1,
    (mul_inv_eq_one₀ two_ne_zero).mpr $ (int.cast_two : ((2 : ℤ) : F) = 2) ▸
      congr_arg coe $ int.floor_int_cast 2,
  -- Now prove that `⌊f(1/2)⌋ = 0`
  (mul_eq_zero.mp $ (h 2⁻¹ 2⁻¹).symm.trans $ (congr_arg f $ mul_eq_zero_of_left
      (int.cast_eq_zero.mpr $ inv_floor_eq_zero one_lt_two) _).trans h0).elim
    (λ h1, h1.symm ▸ int.floor_zero) int.cast_eq_zero.mp),
---- `←`
λ h x y, h.elim
  (λ h, exists.elim h $ λ C h, h.2.symm ▸ h.1.symm ▸
    (int.cast_one : ((1 : ℤ) : R) = 1).symm ▸ (mul_one C).symm)
  (λ h, h.symm ▸ (zero_mul _).symm)⟩

end IMO2010A1
end IMOSL
