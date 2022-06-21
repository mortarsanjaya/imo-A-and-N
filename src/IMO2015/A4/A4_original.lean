import
  IMO2015.A4.A4_general
  data.real.basic 
  data.set.basic

/-
  IMO 2015 A4 (P5), Original Version

  Plainly follows from the generalized version.
  See "A4_general.lean" for the generalized version.
-/

namespace IMO2015A4

theorem final_solution_original :
  set_of fn_eq = ({id, 2 - id} : set (ℝ → ℝ)) :=
    final_solution_general

end IMO2015A4
