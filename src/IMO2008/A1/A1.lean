import algebra.order.positive.ring algebra.group_power.order data.nat.basic tactic.by_contra

/-! # IMO 2008 A1 (P4), Ring Version -/

namespace IMOSL
namespace IMO2008A1

lemma positive_pow_eq_pow {R : Type*} [linear_ordered_ring R]
  {n : ℕ} (h : 0 < n) {a b : {x : R // 0 < x}} : a ^ n = b ^ n ↔ a = b :=
  by simp_rw [← subtype.coe_inj, positive.coe_pow];
    exact pow_left_inj (le_of_lt a.2) (le_of_lt b.2) h



/-- Final solution, general ring version -/
theorem final_solution_general_ring {R : Type*} [linear_ordered_comm_ring R] :
  ∀ f : {x : R // 0 < x} → {x : R // 0 < x}, (∀ p q r s, p * q = r * s →
    (f p ^ 2 + f q ^ 2) * (r ^ 2 + s ^ 2) = (p ^ 2 + q ^ 2) * (f (r ^ 2) + f (s ^ 2)))
      ↔ (f = λ x, x) ∨ ∀ x, x * f x = 1 :=
begin
  ---- First deal with the `←` direction.
  intros f; symmetry; refine ⟨λ h p q r s h0, _, λ h, _⟩,
  { rcases h with rfl | h,
    refl,
    rw [← mul_right_inj (p ^ 2 * q ^ 2), ← mul_assoc, mul_add _ (f p ^ 2), mul_right_comm,
        ← mul_pow, h, mul_assoc, ← mul_pow q, h, one_pow, mul_one, one_mul, add_comm,
        mul_left_comm, mul_right_inj, ← mul_pow, h0, mul_pow, mul_add, mul_right_comm,
        h, one_mul, mul_assoc, h, mul_one, add_comm] },
  
  ---- Deduce `f(x^2) = f(x)^2` and `f(x) = x` or `x f(x) = 1`
  have h0 : ∀ x, f (x ^ 2) = f x ^ 2 :=
    λ x, by replace h := h x x x x rfl;
      rwa [mul_comm, mul_right_inj, ← two_mul, ← two_mul, mul_right_inj, eq_comm] at h,
  replace h := λ x y, h (x ^ 2) (y ^ 2) (x * y) (x * y) (by rw [← sq, mul_pow]),
  simp_rw [h0, ← mul_two, ← mul_assoc, mul_left_inj, ← pow_mul, two_mul] at h,
  replace h0 := h0 1,
  rw [one_pow, sq, self_eq_mul_left] at h0,
  have h1 : ∀ x, f x = x ∨ x * f x = 1 :=
  begin
    intros x; replace h := h x 1,
    rw [mul_one, h0, one_pow, mul_comm, mul_add_one, add_one_mul, pow_add,
        pow_add, mul_assoc, ← mul_assoc, ← mul_pow, mul_comm] at h,
    simp_rw [← subtype.coe_inj, positive.coe_add, positive.coe_mul] at h,
    rw [← eq_sub_iff_add_eq, add_sub_right_comm, ← sub_eq_iff_eq_add, ← mul_sub_one,
        ← mul_sub_one, ← sub_eq_zero, ← sub_mul, mul_eq_zero] at h,
    simp_rw [sub_eq_zero, subtype.coe_inj, positive_pow_eq_pow two_pos] at h,
    revert h; refine or.imp_right (λ h, _),
    rwa [eq_comm, ← positive.coe_one, subtype.coe_inj,
         ← one_pow 2, eq_comm, positive_pow_eq_pow two_pos] at h
  end,

  ---- Finishing
  rw function.funext_iff; by_contra' h2,
  rcases h2 with ⟨⟨a, h2⟩, b, h3⟩,
  have h4 := h1 b; rw or_iff_left h3 at h4,
  replace h := h a b; rw h4 at h,
  replace h4 := h1 (a * b); cases h4 with h4,
  rw [h4, mul_left_inj, add_left_inj, positive_pow_eq_pow four_pos] at h,
  exact h2 h,
  replace h1 := h1 a; rw or_iff_right h2 at h1,
  rw [← mul_right_inj ((a * b) ^ 2), mul_left_comm _ _ (f _ ^ 2), ← mul_pow,
      h4, one_pow, mul_one, mul_comm _ ((a * b) ^ 2), ← mul_assoc, ← pow_add,
      mul_pow, mul_add, mul_right_comm, ← mul_pow, h1, one_pow, one_mul, add_comm,
      add_left_inj, ← mul_pow, ← mul_pow, positive_pow_eq_pow four_pos, mul_assoc,
      mul_right_eq_self, ← sq, eq_comm, ← one_pow 2, positive_pow_eq_pow two_pos] at h,
  apply h3; subst h; rw [one_mul, h0]
end

end IMO2008A1
end IMOSL
