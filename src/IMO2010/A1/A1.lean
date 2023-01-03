import algebra.order.field.basic algebra.order.floor

/-! # IMO 2010 A1 (P1) -/

namespace IMOSL
namespace IMO2010A1

variables {F : Type*} [linear_ordered_field F] [floor_ring F]

/-- For any `r : F` with `1 < r`, we have `⌊r⁻¹⌋ = 0`. -/
lemma inv_floor_eq_zero {r : F} (h : 1 < r) : ⌊r⁻¹⌋ = 0 :=
  by rw [int.floor_eq_iff, int.cast_zero, zero_add, inv_nonneg];
    exact ⟨le_of_lt (lt_trans zero_lt_one h), inv_lt_one h⟩



/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_ring R] [floor_ring R] (f : F → R) :
  (∀ x y : F, f (⌊x⌋ * y) = f x * ⌊f y⌋) ↔ ∃ C : R, (⌊C⌋ = 1 ∨ C = 0) ∧ f = λ _, C :=
begin
  ---- `→` direction
  symmetry; refine ⟨λ h x y, _, λ h, ⟨f 0, _⟩⟩,
  rcases h with ⟨C, h | rfl, rfl⟩,
  rw [h, int.cast_one, mul_one],
  rw zero_mul,

  ---- `←` direction; the case `⌊f(0)⌋ = 1` is easier
  have h0 := h 0 0,
  rw [mul_zero, eq_comm, mul_right_eq_self₀, ← int.cast_one, int.cast_inj] at h0,
  refine ⟨h0, _⟩; cases h0 with h0 h0,
  funext x; replace h := h x 0,
  rwa [mul_zero, h0, int.cast_one, mul_one, eq_comm] at h,

  ---- Now work on the case `f(0) = 0`
  suffices h1 : f 1 = 0,
    funext x; rw h0; replace h := h 1 x;
      rwa [h1, zero_mul, int.floor_one, int.cast_one, one_mul] at h,
  suffices h1 : ⌊f 2⁻¹⌋ = 0,
    replace h := h 2 2⁻¹; rwa [h1, int.cast_zero, mul_zero, ← int.cast_two,
      int.floor_int_cast, int.cast_two, mul_inv_cancel (two_ne_zero : (2 : F) ≠ 0)] at h,
  replace h := h 2⁻¹ 2⁻¹,
  rw [inv_floor_eq_zero (one_lt_two : (1 : F) < 2), int.cast_zero, zero_mul, h0, zero_eq_mul] at h,
  cases h with h h,
  rw [h, int.floor_zero],
  rwa int.cast_eq_zero at h
end

end IMO2010A1
end IMOSL
