import algebra.order.ring.defs

/-! # IMO 2011 A6 (P3) -/

namespace IMOSL
namespace IMO2011A6

/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_comm_ring R]
  {f : R → R} (h : ∀ x y : R, f (x + y) ≤ y * f x + f (f x)) :
  ∀ x : R, x ≤ 0 → f x = 0 :=
---- Blocks of results
have h0 : ∀ t x : R, f (f t) ≤ (f t - x) * f x + f (f x) :=
  λ t x, (h x _).trans_eq' $ congr_arg f (add_sub_cancel'_right x _).symm,
have h0 : ∀ t x : R, 0 ≤ (f t - x) * f x + (f x - t) * f t :=
  λ t x, nonneg_of_le_add_left $ (h0 t x).trans $
    (add_le_add_left (h0 x t) _).trans_eq (add_assoc _ _ _).symm,
have h0 : ∀ x : R, x * f x ≤ 0 :=
  λ x, nonpos_of_neg_nonneg $ (h0 (f x + f x) x).trans_eq $
    (congr_arg2 _ (sub_mul _ _ _) $ congr_arg2 _ (sub_add_cancel' _ _) rfl).trans $
    (add_sub_right_comm _ _ _).symm.trans $ sub_eq_neg_self.mpr $
    add_eq_zero_iff_neg_eq.mpr $ (mul_neg _ _).symm.trans (mul_comm _ _),
have h1 : ∀ x : R, f x ≤ f (f x) :=
  λ x, (congr_arg f (add_zero x).symm).trans_le $
    (h x 0).trans_eq (add_left_eq_self.mpr $ zero_mul _),
have h2 : ∀ x : R, f x ≤ 0 :=
  λ x, le_of_not_lt $ λ h2, (h0 (f x)).not_lt $ mul_pos h2 $ h2.trans_le (h1 x),
have h0 : ∀ x : R, x < 0 → f x = 0 :=
  λ x h3, (h2 x).antisymm $ nonneg_of_mul_nonpos_right (h0 x) h3,
---- Finishing
λ x h3, h3.lt_or_eq.elim (h0 x)
  (λ h4, (congr_arg f h4).trans $ (h2 0).antisymm $ h0 (-1) neg_one_lt_zero ▸ h1 (-1))

end IMO2011A6
end IMOSL
