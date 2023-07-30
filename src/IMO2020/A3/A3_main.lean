import IMO2020.A3.A3_general data.real.sqrt

/-! # IMO 2020 A3 -/

namespace IMOSL
namespace IMO2020A3

/-- Final solution for the real case -/
theorem final_solution :
  is_least ((λ x : extra.fin4 → ℝ, target_val x) ''
    {x | (∀ i : extra.fin4, 0 < x i) ∧ good x}) 8 :=
  target_val_minimum (real.mul_self_sqrt zero_le_three) (real.sqrt_pos.mpr zero_lt_three)

end IMO2020A3
end IMOSL
