import data.nat.sqrt data.nat.parity

/-! # IMO 2016 A5 -/

namespace IMOSL
namespace IMO2016A5

/-- Final solution, part 1 -/
theorem final_solution_part1 (n : ℕ) :
  ∃ a b : ℕ, 0 < b ∧ b ≤ nat.sqrt n + 1 ∧ b ^ 2 * n ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (n + 1) :=
begin
  obtain ⟨r, s, h, rfl⟩ : ∃ r s : ℕ, n ≤ r * r + r + r ∧ r ^ 2 + s = n :=
    ⟨n.sqrt, n - n.sqrt ^ 2, n.sqrt_le_add, nat.add_sub_of_le n.sqrt_le'⟩,
  rw [← sq, add_assoc, add_le_add_iff_left] at h,
  rw nat.sqrt_add_eq' r h; rcases s.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩,

  ---- Case 1: `s` is even
  { rw [← two_mul, ← two_mul, mul_le_mul_left (two_pos : 0 < 2)] at h,
    rcases r.eq_zero_or_pos with rfl | h0,
    refine ⟨0, 1, one_pos, le_refl _, _, zero_le _⟩,
    rw le_zero_iff at h,
    rw [h, one_pow, one_mul, sq, zero_mul, add_zero],
    refine ⟨r ^ 2 + k, r, h0, le_self_add, _⟩,
    rw [mul_add_one, add_sq, sq (r ^ 2), mul_right_comm, ← add_mul, ← two_mul, mul_comm],
    exact ⟨le_self_add, add_le_add_left (pow_le_pow_of_le_left' h 2) _⟩ },
  
  ---- Case 2: `s` is odd
  { rw [nat.succ_le_iff, ← two_mul, mul_lt_mul_left (two_pos : 0 < 2)] at h,
    refine ⟨r ^ 2 + 1 + 2 * k + (r - k), r + 1, r.succ_pos, le_refl _, _⟩,
    rw [add_sq', one_pow, mul_one, add_sq, sq (r ^ 2 + 1 + _), mul_right_comm,
        ← add_mul, add_assoc _ (2 * k), ← mul_add, nat.add_sub_of_le (le_of_lt h),
        add_comm (2 * k), ← add_assoc, mul_add_one],
    refine ⟨le_self_add, add_le_add_left _ _⟩,
    rw add_assoc; exact le_trans (pow_le_pow_of_le_left' (nat.sub_le r k) 2) le_self_add }
end



/-- Final solution, part 2 -/
theorem final_solution_part2 : {n : ℕ | ¬∃ a b : ℕ, 0 < b ∧ b ≤ nat.sqrt n ∧
  b ^ 2 * n ≤ a ^ 2 ∧ a ^ 2 ≤ b ^ 2 * (n + 1)}.infinite :=
begin
  ---- Pick `n = y^2 + 1`, `y > 0` so that `n.sqrt = y`
  have h : function.injective (λ x : ℕ, x.succ ^ 2 + 1) :=
    λ a b h, nat.succ_injective (nat.pow_left_injective one_le_two (add_left_injective 1 h)),
  refine set.infinite_of_injective_forall_mem h (λ x h0, _),
  rcases h0 with ⟨a, b, h0, h1, h2, h3⟩,
  rw nat.sqrt_add_eq' _ (le_add_right (nat.succ_le_succ (zero_le x))) at h1,
  generalize_hyp : x.succ = y at h1 h2 h3; clear h x,

  ---- Get the contradiction
  rw [mul_add_one, ← mul_pow] at h2,
  replace h2 := lt_of_lt_of_le (lt_add_of_pos_right _ (pow_pos h0 2)) h2,
  rw [nat.pow_lt_iff_lt_left one_le_two, ← nat.add_one_le_iff] at h2,
  revert h3; rw [imp_false, not_le, add_assoc, ← bit0, mul_add, ← mul_pow],
  refine lt_of_lt_of_le _ (pow_le_pow_of_le_left' h2 2),
  rw [add_sq, one_pow, nat.lt_succ_iff, add_le_add_iff_left, mul_one, sq, mul_comm],
  exact mul_le_mul_left' (mul_le_mul_left' h1 b) 2
end

end IMO2016A5
end IMOSL
