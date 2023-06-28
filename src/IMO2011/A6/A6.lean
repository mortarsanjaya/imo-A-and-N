import algebra.order.ring.defs

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
    λ t x, (congr_arg f (add_sub_cancel'_right x _).symm).trans_le (h x _),
  replace h0 : ∀ t x : R, 0 ≤ (f t - x) * f x + (f x - t) * f t :=
    λ t x, nonneg_of_le_add_left $ (h0 t x).trans $
      (add_le_add_left (h0 x t) _).trans_eq (add_assoc _ _ _).symm,
  replace h0 : ∀ x : R, x * f x ≤ 0 :=
    λ x, nonpos_of_neg_nonneg $ (h0 (2 * f x) x).trans_eq $
      by rw [← one_sub_mul, mul_right_comm, ← add_mul, ← add_sub_right_comm,
        one_sub_mul, ← add_sub_assoc, ← two_mul, sub_self, zero_sub, neg_mul],

  have h1 : ∀ x : R, f x ≤ f (f x) :=
    λ x, (congr_arg f (add_zero x).symm).trans_le $
      le_of_le_add_of_nonpos_right (h x 0) (zero_mul _).le,
  have h2 : ∀ x : R, f x ≤ 0 :=
    λ x, le_of_not_lt $ λ h2, not_lt_of_le (h0 $ f x) $
      mul_pos h2 $ h2.trans_le $ h1 x,
  replace h0 : ∀ x : R, x < 0 → f x = 0 :=
    λ x h3, (h2 x).antisymm $ nonneg_of_mul_nonpos_right (h0 x) h3,

  ---- Finishing
  intros x h3,
  refine (lt_or_eq_of_le h3).elim (h0 x)
    (λ h4, (congr_arg f h4).trans $ (h2 0).antisymm _),
  rw ← h0 (-1) neg_one_lt_zero; exact h1 (-1)
end

end IMO2011A6
end IMOSL
