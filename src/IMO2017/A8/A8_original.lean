import IMO2017.A8.A8

/-! # IMO 2017 A8, Original Version -/

namespace IMOSL
namespace IMO2017A8

/-- Final solution, original version with rings -/
theorem final_solution_original {R : Type*} [linear_ordered_ring R] [densely_ordered R]
  (f : R → R) (h : ∀ x y : R, 0 < (f x + y) * (f y + x) → f x + y = f y + x) :
    ∀ x y : R, x ≤ y → f y + x ≤ f x + y :=
begin
  obtain ⟨g, rfl⟩ : ∃ g : R → R, id - g = f := ⟨id - f, sub_sub_self id f⟩,
  simp only [pi.sub_def, id.def] at h ⊢,
  intros x y,
  rw [← add_sub_right_comm, ← add_sub_right_comm, add_comm y x, sub_le_sub_iff_left],
  revert x y; apply final_solution_part1,
  simp only []; intros x y h0,
  replace h := h x y,
  rw [← add_sub_right_comm, ← add_sub_right_comm, add_comm, sub_right_inj, add_comm] at h,
  replace h := mt h (ne_of_lt h0),
  split; contrapose! h,
  apply mul_pos_of_neg_of_neg; rwa sub_neg,
  exact lt_trans h h0,
  apply mul_pos; rwa sub_pos,
  exact lt_trans h0 h
end

end IMO2017A8
end IMOSL
