import IMO2011.A3.A3_general data.real.basic

/-!
# IMO 2011 A3, Original Version

## Solution

Follows from the generalized version since 2 is invertible in ℝ.
-/

namespace IMOSL
namespace IMO2011A3

namespace extra

noncomputable instance invertible_two_real :
  invertible (2 : ℝ) := invertible_of_nonzero two_ne_zero

end extra



theorem final_solution_original (f g : ℝ → ℝ) :
  fn_eq f g ↔ (f = 0 ∧ g = 0) ∨ ((∃ C : ℝ, f = λ x, x ^ 2 + C) ∧ g = id) :=
begin
  rw final_solution_general; split,
  { rintros ⟨A, C, rfl, rfl, h, h0⟩,
    simp only [] at h0 ⊢,
    rw [mul_eq_zero, sub_eq_zero] at h,
    rcases h with rfl | rfl,
    rw [zero_mul, zero_add, zero_sub, mul_neg_one, neg_eq_zero] at h0,
    left; rw h0; split; funext x,
    rw [zero_mul, zero_add, pi.zero_apply],
    rw [zero_mul, pi.zero_apply],
    right; split,
    use C; simp only [one_mul],
    funext x; rw [one_mul, id.def] },
  { rintros (⟨rfl, rfl⟩ | ⟨⟨C, rfl⟩, rfl⟩),
    use [0, 0]; simp,
    refl,
    use [1, C]; simp,
    refl },
end

end IMO2011A3
end IMOSL
