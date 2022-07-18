import data.real.basic data.nat.basic algebra.big_operators.intervals

/-! # IMO 2015 A1 -/

open finset

namespace IMOSL
namespace IMO2015A1

def seq_ineq (f : ℕ → ℝ) := ∀ n : ℕ, (n.succ : ℝ) * f n / (f n ^ 2 + n) ≤ f n.succ



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



section results

variables {f : ℕ → ℝ} (f_pos : ∀ n : ℕ, 0 < f n) (fineq : seq_ineq f)
include f_pos fineq

private lemma lem1 (n : ℕ) : (n.succ : ℝ) / f n.succ ≤ f n + n / f n :=
begin
  rw [div_le_iff (f_pos _), ← mul_inv_le_iff, add_div', ← sq, inv_div, ← mul_div_assoc],
  work_on_goal 3 { refine add_pos_of_pos_of_nonneg _ (div_nonneg _ _) },
  exacts [fineq n, (ne_of_gt (f_pos n)), f_pos n, nat.cast_nonneg n, le_of_lt (f_pos n)]
end

private lemma lem2 (n : ℕ) : (n : ℝ) / f n ≤ (range n).sum f :=
begin
  induction n with n n_ih,
  rw [nat.cast_zero, zero_div, range_zero, sum_empty],
  refine le_trans (lem1 f_pos fineq _) (le_of_le_of_eq (add_le_add_left n_ih _) _),
  rw [← eq_sub_iff_add_eq, nat.succ_eq_add_one, sum_range_succ_sub_sum]
end

end results



/-- Final solution -/
theorem final_solution {f : ℕ → ℝ} (f_pos : ∀ n : ℕ, 0 < f n) (fineq : seq_ineq f) :
  ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ (range n).sum f :=
begin
  apply nat.le_induction,
  { rw [nat.cast_bit0, nat.cast_one, bit0, bit0, extra.range_succ_add],
    refine le_trans _ (add_le_add_left (lem2 f_pos fineq 1) _),
    rw [nat.cast_one, one_div],
    exact extra.add_inv_ge_two (f_pos 1) },
  { intros n h h0,
    cases le_or_lt 1 (f n) with h1 h1,
    rw [extra.range_succ_add, nat.cast_add, nat.cast_one, add_comm],
    exact add_le_add h1 h0,
    rw extra.range_succ_add,
    refine le_trans _ (add_le_add_left (lem2 f_pos fineq n) _),
    have h2 := le_trans one_le_two h,
    rw [← nat.sub_add_cancel h2, nat.cast_add, nat.cast_add, nat.cast_one, nat.sub_add_cancel h2,
        div_eq_mul_inv, add_one_mul, add_comm (f n), add_assoc, add_assoc, add_comm _ (f n)],
    refine add_le_add _ (extra.add_inv_ge_two (f_pos n)),
    rw [nat.cast_sub h2, nat.cast_one],
    nth_rewrite 0 ← mul_one (n - 1 : ℝ),
    rw mul_le_mul_left,
    exact le_of_lt (one_lt_inv (f_pos n) h1),
    rwa [lt_sub_iff_add_lt, zero_add, nat.one_lt_cast, nat.lt_iff_add_one_le] }
end

end IMO2015A1
end IMOSL
