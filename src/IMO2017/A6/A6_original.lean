import IMO2017.A6.A6_general data.real.basic

/-!
# IMO 2017 A6 (P2), Original Version.
  
## Solution

Follows from the generalized version, case char(F) ≠ 2, since char(ℝ) = 0 ≠ 2.
-/

namespace IMOSL
namespace IMO2017A6

theorem final_solution_original (f : ℝ → ℝ) :
    fn_eq f ↔ f = 0 ∨ (f = λ x, x - 1) ∨ (f = λ x, 1 - x) :=
  final_solution_general f

end IMO2017A6
end IMOSL
