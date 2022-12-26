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
  set S := {x : F // 0 < x},
  intros f; symmetry; refine ⟨λ h x y, _, λ h, _⟩,
  subst h; simp_rw [inv_inv, sq, mul_inv],
  rw [inv_inv, mul_inv_cancel_left, mul_add, ← mul_assoc, add_comm,
    inv_mul_cancel_comm, ← mul_assoc, inv_mul_cancel_right],

  ---- Setup for the `→` direction.
  have h0 : ∀ x : S, x * f (x ^ 2) * f (f 1) + f (f x) = f x * (f (f (x ^ 2)) + f (f 1)) :=
    λ x, by replace h := h x 1; rwa [one_pow, one_mul, mul_one] at h,
  have h1 := h0 1,
  rw [one_pow, one_mul, mul_add, add_right_inj, self_eq_mul_left] at h1,
  simp_rw [h1, mul_one] at h0,
  replace h1 : ∀ y : S, f (f (y ^ 2))  = f (f y) / f y :=
    λ y, by replace h := h 1 y; rwa [one_pow, one_mul, one_mul, h1, one_mul, mul_one,
      h1, mul_one_add, add_comm, add_right_inj, ← div_eq_iff_eq_mul', eq_comm] at h,
  replace h0 : ∀ y : S, f (y ^ 2) = f y / y :=
    λ y, by replace h0 := h0 y; rwa [mul_add_one, h1, add_comm,
      mul_div_cancel'_right, add_right_inj, ← eq_div_iff_mul_eq''] at h0,

  ---- Reduce to injectivity.
  suffices : function.injective f,
  { funext x; replace h1 := h1 x,
    rw [← h0, h0] at h1,
    replace h1 := this h1,
    rwa [sq, div_eq_mul_inv, mul_right_inj, eq_comm] at h1 },

  ---- Prove injectivity.
  replace h : ∀ {x y c}, f x = c → f y = c → c * f c + f (y * c) = f (x * y) * (2 * (f c / c)) :=
    λ x y c h2 h3, by replace h := h x y;
      rwa [h1, h1, h0, mul_div_cancel'_right, h2, h3, ← two_mul] at h,
  intros a b h2; generalize_hyp h3 : f b = c at h2,
  replace h1 := h h3 h2,
  rwa [h h2 h2, ← sq, mul_comm b, ← h h2 h3, h h3 h3,
    mul_left_inj, ← sq, h0, h0, h2, h3, div_right_inj] at h1
end

end IMO2016A4
end IMOSL
