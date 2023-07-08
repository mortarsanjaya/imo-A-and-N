import extra.integral_domain_without_zero algebra.group_power.basic

/-! # IMO 2016 A4, Ring Version -/

namespace IMOSL
namespace IMO2016A4

/-- Final solution, general version with `extra.domain_without_zero` -/
theorem final_solution_general {R : Type*} [extra.domain_without_zero R] (f : R → R) :
  (∀ x y, x * f (x ^ 2) * f (f y) + f (y * f x) = f (x * y) * (f (f (x ^ 2)) + f (f (y ^ 2))))
    ↔ ∀ x, x * f x = 1 :=
begin
  ---- First deal with the `←` direction.
  symmetry; refine ⟨λ h x y, _, λ h, _⟩,
  { have h0 : ∀ x, f (f x) = x :=
      λ x, by have h0 := h (f x); rwa [← h x, mul_comm, mul_left_inj] at h0,
    rw [h0, h0, h0, ← mul_right_inj (x * y), ← mul_assoc, h, one_mul, mul_add,
        mul_right_comm, ← mul_assoc, ← mul_assoc, ← sq, h, one_mul, ← sq,
        add_comm, add_left_inj, ← mul_left_inj (f x), mul_right_comm,
        mul_assoc x, mul_assoc, h, mul_one, sq, mul_assoc, h, mul_one] },

  ---- Setup for the `→` direction.
  have h0 : ∀ x, x * f (x ^ 2) * f (f 1) + f (f x) = f x * (f (f (x ^ 2)) + f (f 1)) :=
    λ x, by replace h := h x 1; rwa [one_pow, one_mul, mul_one] at h,
  have h1 := h0 1,
  rw [one_pow, one_mul, mul_add, add_right_inj, self_eq_mul_left] at h1,
  simp_rw [h1, mul_one] at h0,
  replace h1 : ∀ y, f y * f (f (y ^ 2)) = f (f y) :=
    λ y, by replace h := h 1 y; rwa [one_pow, one_mul, one_mul, h1, one_mul,
      mul_one, h1, mul_one_add, add_comm, add_right_inj, eq_comm] at h,
  replace h0 : ∀ y, y * f (y ^ 2) = f y :=
    λ y, by replace h0 := h0 y; rwa [mul_add_one, h1, add_comm, add_right_inj] at h0,

  ---- Prove injectivity.
  replace h : ∀ {x y c}, f x = c → f y = c → c * (c * f c + f (y * c)) = 2 * f c * f (x * y) :=
  begin
    intros x y c h2 h3,
    replace h := h x y,
    replace h1 : ∀ {z}, f z = c → c * f (f (z ^ 2)) = f c :=
      λ z h4, by rw [← h4, h1],
    rw [h0, h2, h3] at h,
    rw [h, mul_left_comm, mul_add, h1 h2, h1 h3, mul_comm, ← two_mul]
  end,

  replace h : function.injective f :=
  begin
    intros a b h2; generalize_hyp h3 : f b = c at h2,
    replace h1 := h h3 h2,
    rw [h h2 h2, ← sq, mul_comm b, ← h h2 h3, h h3 h3, mul_right_inj, ← sq] at h1,
    rwa [← h3, ← h0, h1, ← h0 b, mul_left_inj] at h2
  end,

  ---- Finishing
  intros x,
  replace h1 := h1 x,
  rw [← h0 (f x), mul_right_inj] at h1,
  replace h0 := h0 x,
  rwa [h h1, sq, ← mul_assoc, mul_left_eq_self] at h0
end





/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_comm_ring R]
  (f : {x : R // 0 < x} → {x : R // 0 < x}) :
  (∀ x y, x * f (x ^ 2) * f (f y) + f (y * f x) = f (x * y) * (f (f (x ^ 2)) + f (f (y ^ 2))))
    ↔ ∀ x, x * f x = 1 :=
  final_solution_general f

end IMO2016A4
end IMOSL
