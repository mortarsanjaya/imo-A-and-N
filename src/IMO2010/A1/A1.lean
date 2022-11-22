import algebra.order.field.basic algebra.order.floor

/-! # IMO 2010 A1 (P1) -/

namespace IMOSL
namespace IMO2010A1

variables {F : Type*} [linear_ordered_field F] [floor_ring F]
  {R : Type*} [linear_ordered_ring R] [floor_ring R]

/-- For any `r : F` with `1 < r`, we have `⌊r⁻¹⌋ = 0`. -/
lemma inv_floor_eq_zero {r : F} (h : 1 < r) : ⌊r⁻¹⌋ = 0 :=
begin
  rw [int.floor_eq_iff, int.cast_zero, zero_add, inv_nonneg],
  exact ⟨le_of_lt (lt_trans zero_lt_one h), inv_lt_one h⟩
end



/-- Final solution -/
theorem final_solution (f : F → R) : (∀ x y : F, f (⌊x⌋ * y) = f x * ⌊f y⌋) ↔
  ∃ C : R, (C = 0 ∨ ⌊C⌋ = 1) ∧ f = λ _, C :=
begin
  symmetry; refine ⟨λ h x y, _, λ h, ⟨f 0, _⟩⟩,

  ---- `→` direction
  { rcases h with ⟨C, rfl | h, rfl⟩,
    rw zero_mul,
    rw [h, int.cast_one, mul_one] },

  ---- `←` direction
  { have h0 := h 0 0,
    rw [mul_zero, eq_comm, mul_right_eq_self₀] at h0,
    cases h0 with h0 h0,
    
    -- If `⌊f(0)⌋ = 1`, then...
    { rw [← int.cast_one, int.cast_inj] at h0,
      refine ⟨or.inr h0, funext (λ x, _)⟩,
      replace h := h x 0,
      rwa [mul_zero, h0, int.cast_one, mul_one, eq_comm] at h },
  
    -- If `f(0) = 0`, then...
    { refine ⟨or.inl h0, _⟩,
      suffices : f 1 = 0,
      { funext x; replace h := h 1 x,
        rw [this, zero_mul, int.floor_one, int.cast_one, one_mul] at h,
        rw [h, h0] },

      replace h0 : ⌊f 2⁻¹⌋ = 0 :=
      begin
        have h1 := h 2⁻¹ 2⁻¹,
        rw [inv_floor_eq_zero (one_lt_two : (1 : F) < 2), int.cast_zero,
            zero_mul, h0, zero_eq_mul, int.cast_eq_zero] at h1,
        revert h1; refine (or_iff_right_of_imp (λ h1, _)).mp,
        rw [h1, int.floor_zero]
      end,
      have h1 := h ↑(2 : ℤ) 2⁻¹,
      rwa [int.floor_int_cast, int.cast_bit0, int.cast_one, h0, int.cast_zero,
           mul_zero, mul_inv_cancel (two_ne_zero : (2 : F) ≠ 0)] at h1 } }
end

end IMO2010A1
end IMOSL
