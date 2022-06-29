import IMO2017.A6.A6_char_ne_2 data.real.basic

/-!
# IMO 2017 A6 (P2), Original Version.
  
## Solution

Follows from the generalized version, case char(F) ≠ 2, since char(ℝ) = 0 ≠ 2.
-/

namespace IMOSL
namespace IMO2017A6

theorem final_solution_original :
  set_of fn_eq = ({0, 1 - id, id - 1} : set (ℝ → ℝ)) :=
begin
  apply final_solution_char_ne_2,
  rw [ring_char.eq_zero, ne_comm],
  exact two_ne_zero,
end

end IMO2017A6
end IMOSL
