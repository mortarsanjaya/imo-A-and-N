import IMO2011.A3.A3_general data.real.basic

namespace IMOSL
namespace IMO2011A3

/--
  IMO 2011 A3, Original Version

  Follows from the generalized version since 2 is invertible in ℝ.
  See "A3_general.lean" for the generalized version.
-/
theorem final_solution_original (f g : ℝ → ℝ) :
  fn_eq f g ↔ (f = 0 ∧ g = 0) ∨ ((∃ C : ℝ, f = λ x, x ^ 2 + C) ∧ g = id) :=
begin
  apply final_solution_general,
  use 2⁻¹; rw mul_inv_cancel,
  exact two_ne_zero,
end

end IMO2011A3
end IMOSL
