import IMO2017.A8.A8_general

/-! # IMO 2017 A8, Original Version -/

namespace IMOSL
namespace IMO2017A8

/-- Final solution, original version with rings -/
theorem final_solution_original {R : Type*} [linear_ordered_ring R] [densely_ordered R]
  (f : R → R) (h : ∀ x y : R, 0 < (f x + y) * (f y + x) → f x + y = f y + x) :
    ∀ x y : R, x ≤ y → f y + x ≤ f x + y :=
begin
  obtain ⟨g, rfl⟩ : ∃ g : R → R, (λ x, x - g x) = f :=
    ⟨id - f, funext (λ x, sub_sub_self x (f x))⟩,
  intros x y,
  rw [← add_sub_right_comm, ← add_sub_right_comm, add_comm y x, sub_le_sub_iff_left],
  revert x y; refine final_solution_part1 _ (λ x y h0, _),
  replace h := h x y; contrapose h,
  rw [← add_sub_right_comm, ← add_sub_right_comm, add_comm, sub_right_inj, add_comm, not_imp],
  refine ⟨_, h0.ne⟩,
  rw [not_and_distrib, not_le, not_le, ← sub_neg, or_comm, ← sub_pos] at h,
  cases h with h h,
  exacts [mul_pos (h.trans (sub_lt_sub_left h0 (x + y))) h,
    mul_pos_of_neg_of_neg h ((sub_lt_sub_left h0 (x + y)).trans h)]
end

end IMO2017A8
end IMOSL
