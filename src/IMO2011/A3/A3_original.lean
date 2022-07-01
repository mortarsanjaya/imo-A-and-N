import IMO2011.A3.A3_general data.real.basic

/-!
# IMO 2011 A3, Original Version

## Solution

Follows from the generalized version since 2 is invertible in ℝ.
-/

namespace IMOSL
namespace IMO2011A3

theorem final_solution_original (f g : ℝ → ℝ) :
  fn_eq f g ↔ (f = 0 ∧ g = 0) ∨ ((∃ C : ℝ, f = λ x, x ^ 2 + C) ∧ g = id) :=
begin
  apply final_solution_general,
  use 2⁻¹; rw mul_inv_cancel,
  exact two_ne_zero
end

end IMO2011A3
end IMOSL
