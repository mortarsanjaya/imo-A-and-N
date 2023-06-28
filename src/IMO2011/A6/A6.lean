import algebra.order.ring.defs

/-! # IMO 2011 A6 (P3) -/

namespace IMOSL
namespace IMO2011A6

set_option profiler true
set_option profiler.threshold 0.1

/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_comm_ring R]
  {f : R → R} (h : ∀ x y : R, f (x + y) ≤ y * f x + f (f x)) :
  ∀ x : R, x ≤ 0 → f x = 0 :=
begin
  ---- A sequence of results
  have h0 : ∀ t x : R, f (f t) ≤ (f t - x) * f x + f (f x) :=
    λ t x, (congr_arg f (add_sub_cancel'_right x _).symm).trans_le (h x _),
  replace h0 : ∀ x : R, x * f x ≤ 0 := λ x, begin
    have h1 := add_le_add (h0 (2 * f x) x) (h0 x (2 * f x)),
    rwa [add_comm, add_add_add_comm, le_add_iff_nonneg_left, ← one_sub_mul, bit0,
         sub_add_cancel', sub_mul, mul_comm, mul_assoc, neg_one_mul,
         ← sub_eq_add_neg, sub_sub_cancel_left, neg_nonneg] at h1
  end,

  have h1 : ∀ x : R, f x ≤ f (f x) :=
    λ x, (congr_arg f (add_zero x).symm).trans_le $
      le_of_le_add_of_nonpos_right (h x 0) (zero_mul _).le,
  have h2 : ∀ x : R, f x ≤ 0 :=
    λ x, le_of_not_lt $ λ h2, not_lt_of_le (h0 $ f x) $
      mul_pos h2 $ h2.trans_le $ h1 x,
  replace h0 : ∀ x : R, x < 0 → f x = 0 :=
    λ x h3, (h2 x).antisymm (nonneg_of_mul_nonpos_right (h0 x) h3),

  ---- Finishing
  intros x h3,
  refine (lt_or_eq_of_le h3).elim (h0 x)
    (λ h4, (congr_arg f h4).trans $ (h2 0).antisymm _),
  rw ← h0 (-1) neg_one_lt_zero; exact h1 (-1)
end

end IMO2011A6
end IMOSL
