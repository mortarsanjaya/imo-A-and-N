import IMO2017.A8.A8_general algebra.order.ring

/-! # IMO 2017 A8, Original Version -/

namespace IMOSL
namespace IMO2017A8

/-- Final solution, original version -/
theorem final_solution_original {R : Type*} [linear_ordered_ring R] [densely_ordered R]
  {f : R → R} (h : ∀ x y : R, 0 < (f x + y) * (f y + x) → f x + y = f y + x)
  {x y : R} (h0 : x < y) : f y + x ≤ f x + y :=
begin
  revert h0 x y; suffices : good (λ x, x - f x),
  { intros x y h0,
    replace this := final_solution_general this h0,
    simp only [sub_le_iff_le_add'] at this,
    rwa [← add_sub_assoc, le_sub_iff_add_le'] at this },
  simp only [good]; intros x y h0,
  rw [sub_lt_iff_lt_add', ← add_sub_assoc, lt_sub_iff_add_lt'] at h0,
  rw [sub_eq_add_neg, sub_eq_add_neg, add_le_add_iff_left, add_comm, ← not_lt,
      add_le_add_iff_left, ← not_lt, lt_neg_iff_add_neg', neg_lt_iff_pos_add'],
  split; intros h1,
  exacts [ne_of_gt h0 (h x y (mul_pos_of_neg_of_neg h1 (lt_trans h0 h1))),
          ne_of_gt h0 (h x y (mul_pos (lt_trans h1 h0) h1))]
end

end IMO2017A8
end IMOSL
