import algebra.order.field.basic algebra.big_operators.intervals

/-! # IMO 2015 A1 -/

namespace IMOSL
namespace IMO2015A1

open finset

theorem final_solution {F : Type*} [linear_ordered_field F] {a : ℕ → F}
  (h : ∀ k : ℕ, 0 < a k) (h0 : ∀ k : ℕ, (k.succ : F) * a k / (a k ^ 2 + k) ≤ a k.succ) :
  ∀ n : ℕ, 2 ≤ n → (n : F) ≤ (range n).sum a :=
begin
  ---- First replace the inequality condition on `a`
  replace h0 : ∀ k : ℕ, (k.succ : F) / a k.succ ≤ a k + k / a k :=
  begin
    intros k,
    rw [add_div' _ _ _ (ne_of_gt (h k)), div_le_div_iff (h _) (h k), ← sq],
    exact (div_le_iff' (add_pos_of_pos_of_nonneg (pow_pos (h k) 2) k.cast_nonneg)).mp (h0 k)
  end,

  ---- Now induct on `n`, clearing the easy cases
  apply nat.le_induction,
  rw [nat.cast_bit0, nat.cast_one, sum_range_succ, sum_range_one],
  replace h0 := h0 0,
  rw [nat.cast_one, nat.cast_zero, zero_div, add_zero] at h0,
  refine le_trans _ (add_le_add_right h0 _),
  rw [div_add' _ _ _ (ne_of_gt (h 1)), le_div_iff (h 1), ← sq],
  nth_rewrite 2 ← one_pow 2,
  refine le_trans _ (two_mul_le_add_sq _ _),
  rw mul_one,

  intros n h1 h2,
  rw [sum_range_succ, nat.cast_succ],
  cases le_total 1 (a n) with h3 h3,
  exact add_le_add h2 h3,

  ---- The hard cases
  refine le_trans _ (add_le_add_right (_ : (n : F) / a n ≤ _) _),
  rw [div_add' _ _ _ (ne_of_gt (h n)), le_div_iff (h n), add_one_mul,
      ← sub_le_iff_le_add, add_sub_assoc, ← mul_one_sub,
      ← le_sub_iff_add_le', ← mul_one_sub, ← sub_nonneg, ← sub_mul],
  refine mul_nonneg (sub_nonneg.mpr (le_trans h3 _)) (sub_nonneg.mpr h3),
  rw nat.one_le_cast; exact le_trans one_le_two h1,

  clear h1 h2 h3; induction n with n n_ih,
  rw [nat.cast_zero, sum_range_zero, zero_div],
  rw [sum_range_succ, add_comm],
  exact le_trans (h0 n) (add_le_add_left n_ih (a n))
end

end IMO2015A1
end IMOSL
