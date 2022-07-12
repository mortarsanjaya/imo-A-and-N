import data.real.basic

/-! # IMO 2010 A1 (P1) -/

open function
open_locale classical

namespace IMOSL
namespace IMO2010A1

def fn_eq (f : ℝ → ℝ) := ∀ x y : ℝ, f (⌊x⌋ * y) = f x * ⌊f y⌋



namespace extra

/-- For any r : ℝ, 1 < r → ⌊r⌋ = 0. -/
lemma floor_eq_zero_of_eq_one {r : ℝ} (h : 1 < r) : ⌊r⁻¹⌋ = 0 :=
begin
  rw [int.floor_eq_iff, int.cast_zero, zero_add, inv_nonneg]; split,
  exacts [le_of_lt (lt_trans zero_lt_one h), inv_lt_one h]
end

end extra



section results

variables {f : ℝ → ℝ} (feq : fn_eq f)
include feq

/-- Case 1: f(0) ≠ 0 -/
private lemma case_f0_ne_0 (h : f 0 ≠ 0) : ∃ C : ℝ, ⌊C⌋ = 1 ∧ f = const ℝ C :=
begin
  use f 0,
  suffices : ∀ y : ℝ, ⌊f y⌋ = 1,
  { rw and_iff_right (this 0),
    funext,
    replace h1 := feq x 0,
    rwa [mul_zero, this 0, int.cast_one, mul_one, eq_comm] at h1 },
  intros y,
  have h0 := feq 0 y,
  rwa [int.floor_zero, int.cast_zero, zero_mul, eq_comm, mul_right_eq_self₀,
       or_iff_left h, ← int.cast_one, int.cast_inj] at h0
end

/-- Case 2: f(0) = 0 -/
private lemma case_f0_eq_0 (h : f 0 = 0) : f = 0 :=
begin
  suffices : f 1 = 0,
  { funext x,
    have h0 := feq 1 x,
    rwa [this, zero_mul, int.floor_one, int.cast_one, one_mul] at h0 },
  have h0 := feq ↑(2 : ℤ) 2⁻¹,
  rw [int.floor_coe, int.cast_bit0, int.cast_one, mul_inv_cancel] at h0,
  work_on_goal 2 { exact two_ne_zero },
  have h1 := feq 2⁻¹ 2⁻¹,
  rw [extra.floor_eq_zero_of_eq_one one_lt_two, int.cast_zero, zero_mul, h, zero_eq_mul] at h1,
  cases h1 with h1 h1,
  rwa [h1, int.floor_zero, int.cast_zero, mul_zero] at h0,
  rwa [h1, mul_zero] at h0
end

end results



/-- Final solution -/
theorem final_solution (f : ℝ → ℝ) : fn_eq f ↔ f = 0 ∨ ∃ C : ℝ, ⌊C⌋ = 1 ∧ f = const ℝ C :=
begin
  split,
  { intros feq,
    by_cases h : f 0 = 0,
    left; exact case_f0_eq_0 feq h,
    right; exact case_f0_ne_0 feq h },
  { rintros (rfl | ⟨C, h, rfl⟩) x y; simp,
    rw [h, int.cast_one, mul_one] }
end

end IMO2010A1
end IMOSL
