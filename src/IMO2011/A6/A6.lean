import algebra.order.field tactic.linarith

/-! # IMO 2011 A6 (P3) -/

namespace IMOSL
namespace IMO2011A6

/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_comm_ring R]
  {f : R → R} (h : ∀ x y : R, f (x + y) ≤ y * f x + f (f x)) :
  ∀ x : R, x ≤ 0 → f x = 0 :=
begin
  ---- A sequence of results
  have h0 : ∀ t x : R, f (f t) ≤ (f t - x) * f x + f (f x) := λ t x,
    by replace h := h x (f t - x); rwa add_sub_cancel'_right at h,
  replace h0 : ∀ x : R, x * f x ≤ 0 := λ x,
    by linarith [h0 (2 * f x) x, h0 x (2 * f x)],
  have h1 : ∀ x : R, f x ≤ f (f x) := λ x,
    by replace h := h x 0; rwa [add_zero, zero_mul, zero_add] at h,
  have h2 : ∀ x : R, f x ≤ 0 := λ x,
    by contrapose! h1; exact ⟨x, lt_of_le_of_lt (nonpos_of_mul_nonpos_right (h0 (f x)) h1) h1⟩,
  replace h0 : ∀ x : R, x < 0 → f x = 0 := λ x hx,
    le_antisymm (h2 x) (nonneg_of_mul_nonpos_right (h0 x) hx),

  ---- Finishing
  intros x h,
  rw le_iff_lt_or_eq at h; rcases h with h | rfl,
  exact h0 x h,
  refine le_antisymm (h2 0) _,
  rw ← h0 (-1) neg_one_lt_zero; exact h1 (-1)
end

end IMO2011A6
end IMOSL
