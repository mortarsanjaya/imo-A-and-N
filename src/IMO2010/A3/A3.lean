import algebra.order.field.canonical.defs algebra.big_operators.intervals algebra.periodic

/-! # IMO 2010 A3 -/

namespace IMOSL
namespace IMO2010A3

variables {F : Type*} [canonically_linear_ordered_semifield F]

lemma ordered_semifield_AM_GM : ∀ a b : F, 2 * a * b ≤ a ^ 2 + b ^ 2 :=
suffices ∀ a b : F, a ≤ b → 2 * a * b ≤ a ^ 2 + b ^ 2,
from λ a b, (le_total a b).elim (this a b) $
  λ h, (mul_right_comm 2 a b).trans_le $ (this b a h).trans_eq $ add_comm (b ^ 2) (a ^ 2),
λ a b h, exists.elim (le_iff_exists_add.mp h) $
  λ c h0, le_iff_exists_add.mpr ⟨c ^ 2, by rw h0; ring⟩

lemma special_ineq {w x y z c : F} (h : w + x + y ≤ c) (h0 : x + y + z ≤ c) :
  w * y + x * z ≤ (c / 2) ^ 2 :=
begin
  rw [← add_le_add_iff_right (x * (x + y)), add_assoc, ← mul_add, add_comm z],
  refine (add_le_add_left (mul_le_mul_left' h0 _) _).trans _,
  rw [add_comm, ← add_le_add_iff_right ((x + y) * y), add_assoc, ← add_mul, ← add_assoc],
  refine (add_le_add_left (mul_le_mul_right' h _) _).trans _,
  rw [mul_comm, ← mul_add, add_assoc, mul_comm x, ← mul_add, ← sq],
  nth_rewrite 0 ← mul_div_cancel' c two_ne_zero,
  exact ordered_semifield_AM_GM (c / 2) (x + y)
end





open finset

/-- Final solution -/
theorem final_solution (n : ℕ) (c : F) :
  is_greatest ((λ x : ℕ → F, (range (2 * n)).sum (λ i, x i * x (i + 2))) ''
    {x | (∀ j : ℕ, x j + x (j + 1) + x (j + 2) ≤ c) ∧ function.periodic x (2 * n)})
      (n • (c / 2) ^ 2) :=
begin
  refine ⟨⟨λ i, ite (even i) (c / 2) 0, ⟨λ i, _, λ i, if_congr _ rfl rfl⟩, _⟩, _⟩,

  ---- The choice of `x` is good
  { dsimp only []; by_cases h : even i,
    rw [if_pos h, if_neg, add_zero, if_pos, add_halves],
    rwa [nat.even_add_one, nat.even_add_one, not_not],
    rwa [nat.even_add_one, not_not],
    rw [if_neg h, zero_add, if_pos, if_neg, add_zero],
    exact half_le_self (zero_le c),
    rwa [nat.even_add_one, nat.even_add_one, not_not],
    rwa nat.even_add_one },

  ---- The choice of `x` is `2n`-periodic
  rw [nat.even_add, iff_true_intro (even.mul_right even_two n), iff_true],

  ---- The choice of `x` gives the lower bound `n (c/2)^2`
  { dsimp only []; induction n with n h,
    rw [zero_smul, mul_zero, sum_range_zero],
    rw [nat.mul_succ, sum_range_succ, sum_range_succ, h, succ_nsmul', add_assoc, add_right_inj],
    replace h : even (2 * n) := even_two.mul_right n,
    rw [if_pos h, if_pos, if_neg, zero_mul, add_zero, ← sq],
    rwa [nat.even_add_one, not_not],
    rwa [nat.even_add_one, nat.even_add_one, not_not] },

  ---- The upper bound is indeed `n (c/2)^2`
  { rw mem_upper_bounds; intros s h,
    rw set.mem_image at h; rcases h with ⟨x, ⟨h, -⟩, rfl⟩,
    induction n with n h0,
    rw [zero_smul, mul_zero, sum_range_zero],
    rw [nat.mul_succ, sum_range_succ, sum_range_succ, add_assoc, succ_nsmul'],
    exact add_le_add h0 (special_ineq (h $ 2 * n) (h $ 2 * n + 1)) }
end

end IMO2010A3
end IMOSL
