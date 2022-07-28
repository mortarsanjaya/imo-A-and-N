import algebra.order.field algebra.order.floor

/-! # IMO 2010 A1 (P1) -/

open function int
open_locale classical

namespace IMOSL
namespace IMO2010A1

variables {F : Type*} [linear_ordered_field F] [floor_ring F]
  {R : Type*} [linear_ordered_ring R] [floor_ring R]

def fn_eq (f : F → R) := ∀ x y : F, f (⌊x⌋ * y) = f x * ⌊f y⌋



namespace extra

/-- For any r : F with 1 < r, we have ⌊r⁻¹⌋ = 0. -/
lemma inv_floor_eq_zero {r : F} (h : 1 < r) : ⌊r⁻¹⌋ = 0 :=
begin
  rw [floor_eq_iff, cast_zero, zero_add, inv_nonneg],
  exact ⟨le_of_lt (lt_trans zero_lt_one h), inv_lt_one h⟩
end

end extra



/-- Final solution -/
theorem final_solution (f : F → R) : fn_eq f ↔ f = 0 ∨ ∃ C : R, ⌊C⌋ = 1 ∧ f = const F C :=
begin
  split,
  { intros feq,
    have h := feq 0 0,
    rw [mul_zero, eq_comm, mul_right_eq_self₀] at h,
    cases h with h h,
    { right; use f 0,
      rw [← cast_one, int.cast_inj] at h,
      rw and_iff_right h; funext x,
      have h0 := feq x 0,
      rwa [mul_zero, h, cast_one, mul_one, eq_comm] at h0 },
    { left; suffices : f 1 = 0,
      { funext x,
        have h0 := feq 1 x,
        rwa [this, zero_mul, floor_one, cast_one, one_mul] at h0 },
        have h0 : ⌊f 2⁻¹⌋ = 0 :=
        begin
          have h0 := feq 2⁻¹ 2⁻¹,
          rwa [extra.inv_floor_eq_zero (one_lt_two : (1 : F) < 2), cast_zero, zero_mul, h,
               zero_eq_mul, or_iff_right_of_imp, cast_eq_zero] at h0,
          intros h1; rw [h1, floor_zero, cast_zero]
        end,
        have h1 := feq ↑(2 : ℤ) 2⁻¹,
        rwa [floor_coe, cast_bit0, cast_one, h0, cast_zero, mul_zero, mul_inv_cancel] at h1,
        exact two_ne_zero } },
  { rintros (rfl | ⟨C, h, rfl⟩) x y,
    rw [pi.zero_apply, pi.zero_apply, zero_mul],
    rw [h, cast_one, mul_one] }
end

end IMO2010A1
end IMOSL
