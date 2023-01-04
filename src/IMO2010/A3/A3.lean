import algebra.field.basic algebra.big_operators.intervals algebra.periodic
  algebra.order.field.canonical.defs

/-! # IMO 2010 A3 -/

namespace IMOSL
namespace IMO2010A3

set_option profiler true
set_option profiler.threshold 0.2

open finset function

variables {F : Type*} [canonically_linear_ordered_semifield F]

section extra_lemmas

private lemma AM_GM (a b : F) : 2 * a * b ≤ a ^ 2 + b ^ 2 :=
begin
  rw le_iff_exists_add,
  cases le_total a b with h h; rw le_iff_exists_add at h;
    rcases h with ⟨c, rfl⟩; use c ^ 2,
  rw [add_sq, ← add_assoc, ← add_assoc, ← two_mul, sq, ← mul_assoc, ← mul_add],
  rw [add_sq, add_right_comm, add_right_comm _ _ (b ^ 2),
      ← two_mul, sq, ← mul_assoc, ← mul_add, mul_right_comm]
end

private lemma special_ineq {w x y z c : F} (h : w + x + y ≤ c) (h0 : x + y + z ≤ c) :
  w * y + x * z ≤ (c / 2) ^ 2 :=
begin
  rw [← add_le_add_iff_right (x * (x + y)), add_assoc, ← mul_add, add_comm z],
  refine le_trans (add_le_add_left (mul_le_mul_left' h0 _) _) _; clear h0 z,
  rw [add_comm, ← add_le_add_iff_right ((x + y) * y), add_assoc, ← add_mul, ← add_assoc],
  refine le_trans (add_le_add_left (mul_le_mul_right' h _) _) _; clear h w,
  rw [mul_comm, ← mul_add, add_assoc, mul_comm x, ← mul_add, ← sq],
  nth_rewrite 0 ← mul_div_cancel' c two_ne_zero,
  exact AM_GM (c / 2) (x + y)
end

end extra_lemmas







/-- Final solution -/
theorem final_solution (n : ℕ) (c : F) :
  is_greatest ((λ x : ℕ → F, (range (2 * n)).sum (λ i, x i * x (i + 2))) ''
    {x | (∀ j : ℕ, x j + x (j + 1) + x (j + 2) ≤ c) ∧ periodic x (2 * n)})
      (n • (c / 2) ^ 2) :=
begin
  refine ⟨⟨λ i, ite (even i) (c / 2) 0, ⟨λ i, _, λ i, if_congr _ rfl rfl⟩, _⟩, _⟩,

  ---- The choice of `x` is good
  { simp_rw [nat.even_add, even_two, nat.not_even_one, iff_true, iff_false],
    rw ite_not; by_cases h : even i,
    rw [if_pos h, if_pos h, add_zero, add_halves],
    rw [if_neg h, zero_add, add_zero, if_neg h],
    exact half_le_self (zero_le c) },

  ---- The choice of `x` is `2n`-periodic
  rw [nat.even_add, iff_true_intro (even.mul_right even_two n), iff_true],

  ---- The choice of `x` gives the lower bound `n (c/2)^2`
  { simp only []; induction n with n h,
    rw [zero_smul, mul_zero, sum_range_zero],
    rw [nat.mul_succ, sum_range_succ, sum_range_succ, h, succ_nsmul', add_assoc, add_right_inj],
    replace h : even (2 * n) := even_two.mul_right n,
    rw [if_pos h, if_pos, if_neg, zero_mul, add_zero, ← sq],
    rw [nat.even_add, iff_true_intro h, true_iff]; exact nat.not_even_one,
    rw [nat.even_add, iff_true_intro h, true_iff]; exact even_two },

  ---- The upper bound is indeed `n (c/2)^2`
  { rw mem_upper_bounds; intros s h,
    rw set.mem_image at h; rcases h with ⟨x, ⟨h, -⟩, rfl⟩,
    induction n with n h0,
    rw [zero_smul, mul_zero, sum_range_zero],
    rw [nat.mul_succ, sum_range_succ, sum_range_succ, add_assoc, succ_nsmul'],
    exact add_le_add h0 (special_ineq (h $ 2 * n) (h $ 2 * n + 1)) }
end

/-


/-- Final solution -/
theorem final_solution (n : ℕ) :
  is_greatest ((λ x : ℕ → ℝ≥0, target_sum x n) '' {x | good x ∧ periodic x (2 * n)})
    ((n : ℝ≥0) / 4) :=
begin
  refine ⟨⟨_, ⟨bin_even_good, λ k, _⟩, bin_even_target_sum n⟩, λ a h, _⟩,
  simp only [nat.even_add, even_two_mul, iff_true],
  rcases h with ⟨x, ⟨h, -⟩, rfl⟩,
  exact target_sum_good_bound h n
end
-/

end IMO2010A3
end IMOSL
