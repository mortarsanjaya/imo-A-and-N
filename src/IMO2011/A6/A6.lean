import algebra.order.field.basic tactic.linarith

/-! # IMO 2011 A6 (P3) -/

namespace IMOSL
namespace IMO2011A6

/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_comm_ring R]
  {f : R → R} (h : ∀ x y : R, f (x + y) ≤ y * f x + f (f x)) :
  ∀ x : R, x ≤ 0 → f x = 0 :=
begin
  ---- A sequence of results
  have h0 : ∀ t x : R, f (f t) ≤ (f t - x) * f x + f (f x) :=
    λ t x, le_of_eq_of_le (congr_arg f (add_sub_cancel'_right x _).symm) (h x _),
  replace h0 : ∀ x : R, x * f x ≤ 0 :=
    λ x, by linarith [h0 (2 * f x) x, h0 x (2 * f x)],
  have h1 : ∀ x : R, f x ≤ f (f x) :=
    λ x, by replace h := h x 0; rwa [add_zero, zero_mul, zero_add] at h,
  have h2 : ∀ x : R, f x ≤ 0 :=
    λ x, le_of_not_lt (λ h2, not_lt_of_le (h0 $ f x) $
      mul_pos h2 $ lt_of_lt_of_le h2 $ h1 x),
  replace h0 : ∀ x : R, x < 0 → f x = 0 :=
    λ x h3, le_antisymm (h2 x) (nonneg_of_mul_nonpos_right (h0 x) h3),

  ---- Finishing
  intros x h3,
  refine (lt_or_eq_of_le h3).elim (h0 x)
    (λ h4, (congr_arg f h4).trans $ le_antisymm (h2 0) _),
  rw ← h0 (-1) neg_one_lt_zero; exact h1 (-1)
end

end IMO2011A6
end IMOSL
