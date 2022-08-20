import data.real.basic algebra.big_operators.intervals

/-! # IMO 2015 A1 -/

namespace IMOSL
namespace IMO2015A1

open finset

def seq_ineq (f : ℕ → ℝ) := ∀ n : ℕ, (n.succ : ℝ) * f n / (f n ^ 2 + n) ≤ f n.succ



namespace extra

lemma add_inv_ge_two {x : ℝ} (h : 0 < x) : (2 : ℝ) ≤ x⁻¹ + x :=
begin
  rw [← mul_le_mul_right h, add_mul, inv_mul_cancel (ne_of_gt h), ← sub_nonneg],
  apply le_of_le_of_eq (sq_nonneg (x - 1)),
  rw [sub_sq', mul_one, one_pow, sq, add_comm]
end

end extra



section results

variables {f : ℕ → ℝ} (fpos : ∀ n : ℕ, 0 < f n) (fineq : seq_ineq f)
include fpos fineq

private lemma lem1 (n : ℕ) : (n.succ : ℝ) / f n.succ ≤ f n + n / f n :=
begin
  rw [div_le_iff (fpos _), ← mul_inv_le_iff, add_div', ← sq, inv_div, ← mul_div_assoc],
  work_on_goal 3 { refine add_pos_of_pos_of_nonneg _ (div_nonneg _ _) },
  exacts [fineq n, (ne_of_gt (fpos n)), fpos n, nat.cast_nonneg n, le_of_lt (fpos n)]
end

private lemma lem2 (n : ℕ) : (n : ℝ) / f n ≤ (range n).sum f :=
begin
  induction n with n n_ih,
  rw [nat.cast_zero, zero_div, range_zero, sum_empty],
  refine le_trans (lem1 fpos fineq _) (le_of_le_of_eq (add_le_add_left n_ih _) _),
  rw [← eq_sub_iff_add_eq, nat.succ_eq_add_one, sum_range_succ_sub_sum]
end

end results



/-- Final solution -/
theorem final_solution {f : ℕ → ℝ} (fpos : ∀ n : ℕ, 0 < f n) (fineq : seq_ineq f) :
  ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ (range n).sum f :=
begin
  apply nat.le_induction,
  { rw [nat.cast_bit0, nat.cast_one, sum_range_succ],
    refine le_trans (extra.add_inv_ge_two (fpos 1)) (add_le_add_right _ _),
    convert lem2 fpos fineq 1,
    rw [nat.cast_one, one_div] },
  { intros n h h0,
    cases le_or_lt 1 (f n) with h1 h1,
    rw [sum_range_succ, nat.cast_add, nat.cast_one],
    exact add_le_add h0 h1,
    rw sum_range_succ; refine le_trans _ (add_le_add_right (lem2 fpos fineq n) _),
    have h2 := le_trans one_le_two h,
    rw [← nat.sub_add_cancel h2, nat.cast_add, nat.cast_add, nat.cast_one,
        nat.sub_add_cancel h2, div_eq_mul_inv, add_one_mul, add_assoc, add_assoc],
    refine add_le_add _ (extra.add_inv_ge_two (fpos n)),
    rw [nat.cast_sub h2, nat.cast_one],
    nth_rewrite 0 ← mul_one (n - 1 : ℝ),
    rw mul_le_mul_left,
    exact le_of_lt (one_lt_inv (fpos n) h1),
    rwa [lt_sub_iff_add_lt, zero_add, nat.one_lt_cast, nat.lt_iff_add_one_le] }
end

end IMO2015A1
end IMOSL
