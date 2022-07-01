import data.real.basic data.nat.basic algebra.big_operators.intervals

/-!
# IMO 2015 A1

Let a_1, a_2, … be a sequence of positive real numbers such that, for all k ≥ 1,
  a_{k + 1} ≥ k a_k/(a_k^2 + k - 1).
Prove that a_1 + a_2 + … + a_n ≥ n for every n ≥ 2.

## Solution

See <http://www.imo-official.org/problems/IMO2015SL.pdf>.
We will follow the official Solution.

## Implementation details

We will use ℕ = {0, 1, …} indexing instead of ℕ+ = {1, 2, …} indexing.
-/

open finset

namespace IMOSL
namespace IMO2015A1



namespace extra

lemma add_inv_ge_two {x : ℝ} (h : 0 < x) : (2 : ℝ) ≤ x + x⁻¹ :=
begin
  rw [← mul_le_mul_right h, add_mul, inv_mul_cancel (ne_of_gt h),
      ← add_le_add_iff_left (-(2 * x)), neg_add_self],
  apply le_of_le_of_eq (sq_nonneg (x - 1)),
  ring
end

lemma range_succ_add {β : Type*} [add_comm_group β] (f : ℕ → β) (n : ℕ) :
    (range (n + 1)).sum f = f n + (range n).sum f :=
  by rw [← sub_eq_iff_eq_add, sum_range_succ_sub_sum]

end extra



/-- Final solution -/
theorem final_solution (f : ℕ → ℝ) (h : ∀ n : ℕ, 0 < f n)
    (h0 : ∀ k : ℕ, (k.succ : ℝ) * f k / (f k ^ 2 + k) ≤ f (k.succ)) :
  ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ (range n).sum f :=
begin
  have h1 : ∀ m : ℕ, (m : ℝ) / f m ≤ (range m).sum f :=
  begin
    intros m; induction m with m m_ih,
    rw [nat.cast_zero, zero_div, range_zero, sum_empty],
    suffices : (m.succ : ℝ) / f m.succ ≤ f m + m / f m,
    { refine le_trans this (le_of_le_of_eq (add_le_add_left m_ih _) _),
      rw [← eq_sub_iff_add_eq, nat.succ_eq_add_one, sum_range_succ_sub_sum] },
    rw [div_le_iff (h _), ← mul_inv_le_iff, add_div' _ _ _ (ne_of_gt (h m)),
        ← sq, inv_div, ← mul_div_assoc],
    exact h0 m,
    exact add_pos_of_pos_of_nonneg (h m) (div_nonneg (nat.cast_nonneg m) (le_of_lt (h m)))
  end,
  apply nat.le_induction,
  { rw [nat.cast_bit0, nat.cast_one],
    change 2 with 1 + 1,
    rw extra.range_succ_add,
    refine le_trans _ (add_le_add_left (h1 1) _),
    rw [nat.cast_one, one_div],
    exact extra.add_inv_ge_two (h 1) },
  { intros n h2 h3,
    cases le_or_lt 1 (f n) with h4 h4,
    { rw [extra.range_succ_add, nat.cast_add, nat.cast_one, add_comm],
      exact add_le_add h4 h3 },
    { rw extra.range_succ_add,
      refine le_trans _ (add_le_add_left (h1 n) _),
      rw [← nat.sub_add_cancel (le_trans one_le_two h2), nat.cast_add, nat.cast_add,
          nat.cast_one, nat.sub_add_cancel (le_trans one_le_two h2), div_eq_mul_inv,
          add_one_mul, add_comm (f n), add_assoc, add_assoc, add_comm _ (f n)],
      refine add_le_add _ (extra.add_inv_ge_two (h n)),
      rw [nat.cast_sub (le_trans one_le_two h2), nat.cast_one],
      nth_rewrite 0 ← mul_one (n - 1 : ℝ),
      rw mul_le_mul_left,
      exact le_of_lt (one_lt_inv (h n) h4),
      rwa [lt_sub_iff_add_lt, zero_add, nat.one_lt_cast, nat.lt_iff_add_one_le] } }
end




end IMO2015A1
end IMOSL
