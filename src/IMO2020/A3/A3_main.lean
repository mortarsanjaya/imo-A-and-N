import IMO2020.A3.A3_lb data.real.sqrt tactic.fin_cases

/-! # IMO 2020 A3 -/

namespace IMOSL
namespace IMO2020A3

lemma exists_good_target_val_eq_bound
  {F : Type*} [linear_ordered_field F] (h : ∃ c : F, 0 < c ∧ c + c⁻¹ = 4) :
  ∃ x : fin 4 → F, (∀ i, 0 < x i) ∧ good x ∧ target_val x = 8 :=
begin
  rcases h with ⟨c, h, h0⟩,
  refine ⟨![c, 1, c, 1], λ i, _, _, _⟩,
  { fin_cases i,
    exacts [h, one_pos, h, one_pos] },
  { calc (c + c) * 2 = (2 * c) * 2 : congr_arg2 has_mul.mul (two_mul c).symm rfl
    ... = 4 * c : by rw [mul_right_comm, two_mul, ← bit0]
    ... = c * c + 1 * 1 : by rw [mul_one, ← h0, add_mul, inv_mul_cancel (ne_of_gt h)] },
  { calc c / 1 + 1 / c + c / 1 + 1 / c = c + c⁻¹ + c + c⁻¹ : by rw [div_one, one_div]
    ... = 4 + 4 : by rw [add_assoc _ c, h0] }
end

lemma real_two_add_sqrt_three_prop : (2 + real.sqrt 3) + (2 + real.sqrt 3)⁻¹ = 4 :=
begin
  rw [eq_comm, bit0, add_assoc, add_right_inj, ← sub_eq_iff_eq_add'],
  apply eq_inv_of_mul_eq_one_right,
  rw [← sq_sub_sq, real.sq_sqrt zero_le_three, sq, two_mul,
      bit1, add_sub_add_left_eq_sub, bit0, add_sub_cancel]
end



/-- Final solution -/
theorem final_solution :
  is_least ((λ x : fin 4 → ℝ, target_val x) '' {x | (∀ i : fin 4, 0 < x i) ∧ good x}) 8 :=
  ⟨exists.elim (exists_good_target_val_eq_bound ⟨2 + real.sqrt 3,
    add_pos_of_pos_of_nonneg two_pos (real.sqrt_nonneg 3), real_two_add_sqrt_three_prop⟩) $
     λ x h, ⟨x, ⟨h.1, h.2.1⟩, h.2.2⟩,
  λ c h, exists.elim h $ λ x h0, le_of_le_of_eq (target_val_good_bound h0.1.1 h0.1.2) h0.2⟩

end IMO2020A3
end IMOSL
