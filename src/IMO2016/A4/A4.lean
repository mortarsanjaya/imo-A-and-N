import algebra.order.positive.field

/-! # IMO 2016 A4 -/

namespace IMOSL
namespace IMO2016A4

/-- Final solution -/
theorem final_solution {F : Type*} [linear_ordered_field F] :
  ∀ f : {x : F // 0 < x} → {x : F // 0 < x},
    (∀ x y : {x : F // 0 < x}, x * f (x ^ 2) * f (f y) + f (y * f x)
      = f (x * y) * (f (f (x ^ 2)) + f (f (y ^ 2))))
    ↔ f = has_inv.inv :=
begin
  ---- First deal with the `←` direction.
  intros f; symmetry; refine ⟨λ h x y, _, λ h, _⟩,
  subst h; simp_rw [sq, mul_inv, inv_inv, mul_inv_cancel_left, mul_add, mul_left_comm (x⁻¹ * y⁻¹),
    inv_mul_cancel_comm, inv_mul_cancel_right, mul_comm x, mul_comm y, add_comm (x⁻¹ * y)],
  
  ---- Setup for the `→` direction.
  have h0 := λ x, h x 1,
  simp_rw [one_pow, one_mul, mul_one] at h0,
  have h1 := h0 1,
  rw [one_pow, one_mul, mul_add, add_right_inj, self_eq_mul_left] at h1,
  simp_rw [h1, mul_one] at h0,
  have h2 := h 1,
  simp_rw [one_pow, h1, one_mul, mul_one, add_comm (1 : {x : F // 0 < x})] at h2,
  replace h1 : ∀ y, f (y ^ 2) = f y / y :=
    λ y, by replace h1 := h2 y;
      rwa [← h0, add_comm, add_left_inj, ← div_eq_iff_eq_mul', eq_comm] at h1,
  simp_rw [mul_add_one, add_left_inj, ← div_eq_iff_eq_mul'] at h2,

  ---- Reduce to injectivity.
  suffices : function.injective f,
  { funext x; replace h2 := h2 x,
    rw [h1, ← h1] at h2,
    replace h2 := this h2,
    rwa [sq, div_eq_mul_inv, mul_right_inj] at h2 },

  ---- Prove injectivity.
  replace h : ∀ {x y c}, f x = c → f y = c → c * f c + f (y * c) = f (x * y) * (2 * (f c / c)) :=
    λ x y c h3 h4, by replace h := h x y;
      rwa [← h2, ← h2, h1, mul_div_cancel'_right, h3, h4, ← two_mul] at h,
  clear h0; intros a b h0,
  generalize_hyp h3 : f b = c at h0,
  replace h2 := h h3 h0,
  rwa [h h0 h0, ← sq, mul_comm b, ← h h0 h3, h h3 h3,
    mul_left_inj, ← sq, h1, h1, h0, h3, div_right_inj] at h2
end

end IMO2016A4
end IMOSL
