import IMO2006.A6.A6_general data.real.sqrt

/-! # IMO 2006 A6 (P3) -/

namespace IMOSL
namespace IMO2006A6

section general_field

variables {F : Type*} [linear_ordered_field F] {sqrt2 : F} (h : 0 ≤ sqrt2) (h0 : sqrt2 ^ 2 = 2)
include h h0

lemma field_good_iff (M : F) : good M ↔ 9 * sqrt2 / 32 ≤ M :=
  (good_iff h h0 M).trans (div_le_iff $ by norm_num).symm

lemma field_good_num : good (9 * sqrt2 / 32) :=
  (field_good_iff h h0 _).mpr (le_refl _)

lemma field_good_minimum {F : Type*} [linear_ordered_field F]
  {sqrt2 : F} (h : 0 ≤ sqrt2) (h0 : sqrt2 ^ 2 = 2) :
  is_least (good : F → Prop) (9 * sqrt2 / 32) := 
  ⟨field_good_num h h0, λ M, (field_good_iff h h0 M).mp⟩

end general_field



/-- Final solution for the real case -/
theorem final_solution : is_least (good : ℝ → Prop) (9 * real.sqrt 2 / 32) :=
  field_good_minimum (real.sqrt_nonneg 2) (real.sq_sqrt zero_le_two)

end IMO2006A6
end IMOSL
