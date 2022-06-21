import
  IMO2011.A3.A3_general
  data.real.basic
  data.set.basic

/-
  IMO 2011 A3, Original Version

  Follows from the generalized version since 2 is invertible in ℝ.
  See "A3_general.lean" for the generalized version.
-/

namespace IMO2011A3

theorem final_solution_original :
  set_of (λ s : (ℝ → ℝ) × (ℝ → ℝ), fn_eq s.fst s.snd) =
    {(0, 0)} ∪ (λ C : ℝ, ((λ x : ℝ, x ^ 2) + function.const ℝ C, id)) '' set.univ :=
begin
  apply final_solution_general,
  use 2⁻¹; rw mul_inv_cancel,
  exact two_ne_zero,
end

end IMO2011A3