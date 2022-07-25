import algebra.char_p.basic data.real.nnreal

open_locale nnreal

namespace IMOSL
namespace extra

/-- Copy of `ring_hom_semifield_char_zero_empty` for ℝ≥0.
  TODO: Replace with linear ordered semifield instance for ℝ≥0,
    or delete this file if the instance becomes available in mathlib. -/
instance ring_hom_nnreal_empty {R : Type*} [nontrivial R] [semiring R]
  {p : ℕ} [fact (p ≠ 0)] [char_p R p] : is_empty (ℝ≥0 →+* R) :=
{ false := λ φ,
  begin
    have h := map_nat_cast φ p,
    rw char_p.cast_eq_zero R at h,
    replace h := mul_eq_zero_of_left h (φ p⁻¹),
    rw [← map_mul, mul_inv_cancel, map_one] at h,
    exact one_ne_zero h,
    rw nat.cast_ne_zero,
    exact fact.out (p ≠ 0)
  end }

end extra
end IMOSL
