import algebra.big_operators.intervals algebra.big_operators.order algebra.big_operators.ring

/-! # IMO 2021 A5 -/

namespace IMOSL
namespace IMO2021A5

open finset

variables {F : Type*} [linear_ordered_field F]

private lemma bound1 {a : ℕ → F} (h : ∀ n : ℕ, 0 < a n) {n : ℕ} (h0 : (range n.succ).sum a ≤ 1) :
  a n / (1 - a n) * ((range n).sum a) ^ 2 ≤ (((range n.succ).sum a) ^ 3 - ((range n).sum a) ^ 3) / 3 :=
begin
  rcases nat.eq_zero_or_pos n with rfl | h1,
  rw [sum_range_zero, sum_range_one, zero_pow two_pos, mul_zero, zero_pow three_pos, sub_zero],
  exact div_nonneg (pow_nonneg (le_of_lt (h 0)) 3) zero_le_three,
  rw [sum_range_succ, add_comm] at h0 ⊢,
  have h2 : 0 ≤ (range n).sum a := sum_nonneg (λ i _, le_of_lt (h i)),
  replace h := h n,
  generalizes [hx : a n = x, hy : (range n).sum a = y],
  rw ← hx at h0 h; rw ← hy at h0 h2,
  clear h1 hx hy a n,
  suffices : x / (1 - x) * y ^ 2 ≤ x ^ 2 * y + x * y ^ 2,
  { apply le_trans this,
    rw ← sub_nonneg; ring_nf,
    exact mul_nonneg (div_nonneg zero_le_one zero_le_three) (pow_nonneg (le_of_lt h) 3) },
  rw [← le_sub_iff_add_le', le_iff_eq_or_lt] at h0,
  rcases h0 with rfl | h0,
  { rw le_iff_eq_or_lt at h2,
    rcases h2 with h2 | h2,
    rw [← h2, sq, mul_zero, mul_zero, ← add_mul, mul_zero],
    rw [sq, ← mul_assoc, div_mul_cancel x (ne_of_gt h2), sq, mul_assoc,
        ← mul_add, ← add_mul, add_sub_cancel'_right, one_mul] },
  { have h1 := ne_of_gt (lt_of_le_of_lt h2 h0),
    rw [div_eq_mul_inv, mul_right_comm, ← sub_le_iff_le_add, ← mul_sub_one, inv_eq_one_div,
        div_sub_one h1, sub_sub_cancel, ← mul_div_assoc, mul_right_comm, ← sq, sq y,
        ← mul_assoc, mul_div_assoc, ← sub_nonpos, ← mul_sub_one, div_sub_one h1],
    refine mul_nonpos_of_nonneg_of_nonpos (mul_nonneg _ h2) (div_nonpos_of_nonpos_of_nonneg _ _),
    exacts [sq_nonneg x, le_of_lt (by rwa sub_neg), le_trans h2 (le_of_lt h0)] }
end



/-- Final solution -/
theorem final_solution {a : ℕ → F} (h : ∀ n : ℕ, 0 < a n) {n : ℕ} (h0 : (range n).sum a ≤ 1) :
  (range n).sum (λ k, a k / (1 - a k) * ((range k).sum a) ^ 2) < 1 / 3 :=
begin
  rcases nat.eq_zero_or_pos n with rfl | h1,
  rw [sum_range_zero, one_div, inv_pos]; exact three_pos,
  refine lt_of_lt_of_le (sum_lt_sum (λ i h2, bound1 h _) _) _,
  { rw [mem_range, ← nat.succ_le_iff] at h2,
    refine le_trans _ h0,
    rw [← sum_range_add_sum_Ico a h2, le_add_iff_nonneg_right],
    exact sum_nonneg (λ i _, (le_of_lt (h i))) },
  { use 0; split,
    rwa mem_range,
    rw [sum_range_zero, zero_pow two_pos, mul_zero, zero_pow three_pos, sub_zero, sum_range_one],
    exact div_pos (pow_pos (h 0) 3) three_pos },
  { rw [← sum_div, sum_range_sub (λ i, (range i).sum a ^ 3)],
    simp only [sub_zero, sum_range_zero, zero_pow three_pos],
    exact div_le_div_of_le zero_le_three (pow_le_one 3 (sum_nonneg (λ i _, le_of_lt (h i))) h0) }
end

end IMO2021A5
end IMOSL
