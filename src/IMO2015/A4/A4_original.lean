import IMO2015.A4.A4_general data.real.basic

/-! # IMO 2015 A4 (P5), Original Version -/

namespace IMOSL
namespace IMO2015A4

theorem final_solution_original (f : ℝ → ℝ) : fn_eq f ↔ f = id ∨ f = 2 - id :=
    final_solution_general f

end IMO2015A4
end IMOSL
