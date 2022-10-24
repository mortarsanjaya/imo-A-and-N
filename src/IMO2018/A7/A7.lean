import analysis.mean_inequalities extra.periodic.big_operators extra.real_prop.real_quadratic_sol

/-! # IMO 2018 A7 -/

namespace IMOSL
namespace IMO2018A7

open finset nnreal function
open_locale nnreal

noncomputable def target_sum (q : ℝ≥0) (a : ℕ → ℝ≥0) (n : ℕ) :=
  (range (2 * n)).sum (λ i, (a i / (a (i + 1) + q)) ^ (1 / 3 : ℝ))



section extra_lemmas

private lemma cauchy_schwarz_engel {a b : ℕ → ℝ≥0} (hb : ∀ i : ℕ, 0 < b i) (n : ℕ) :
  (range n).sum a ^ 2 / (range n).sum b ≤ (range n).sum (λ i, a i ^ 2 / b i) :=
begin
  apply div_le_of_le_mul,
  rw [← le_sqrt_iff, sqrt_eq_rpow, mul_rpow],
  convert nnreal.inner_le_Lp_mul_Lq (range n)
    (λ i, a i / sqrt (b i)) (λ i, sqrt (b i)) _,
  funext i; symmetry; refine div_mul_cancel _ (ne_of_gt _),
  rw sqrt_eq_rpow; exact rpow_pos (hb i),
  funext i; rw [div_rpow, rpow_two, rpow_two, sq_sqrt],
  funext i; rw [rpow_two, sq_sqrt],
  rw real.is_conjugate_exponent_iff; norm_num
end

end extra_lemmas



section upper_bound

variables {a : ℕ → ℝ≥0} {n : ℕ} (hn : 0 < n) (h : periodic a n) {q t s : ℝ≥0} (hq : 0 < q)
  (ht : (range n).sum (λ i, sqrt (a i)) = n • t) (hs : (range n).sum (λ i, (a i + q)⁻¹) = n • s)
include hn h hq ht hs
  
private lemma holder_target :
  (range n).sum (λ i, (a i / (a (i + 1) + q)) ^ (1 / 3 : ℝ)) ≤
    n • (t ^ (2 / 3 : ℝ) * s ^ (1 / 3 : ℝ)) :=
begin
  have X : (3 / 2 : ℝ).is_conjugate_exponent 3 :=
    by rw real.is_conjugate_exponent_iff; norm_num,
  convert nnreal.inner_le_Lp_mul_Lq (range n)
    (λ i, a i ^ (1 / 3 : ℝ)) (λ i, (a (i + 1) + q)⁻¹ ^ (1 / 3 : ℝ)) X,
  funext; rw [div_eq_mul_inv, mul_rpow],
  replace X : (3 : ℝ) ≠ 0 := three_ne_zero,
  rw [one_div_div, ← rpow_eq_rpow_iff X, nsmul_eq_mul, mul_rpow, ← rpow_mul, inv_mul_cancel X,
      rpow_one, mul_rpow, ← rpow_mul, div_mul_cancel 2 X, ← rpow_mul, div_mul_cancel 1 X, rpow_one],
  conv_rhs {
    congr, congr, congr, skip, funext, rw [← rpow_mul, mul_div, inv_mul_cancel X, ← sqrt_eq_rpow],
    skip, skip, congr, skip, funext, rw [← rpow_mul, inv_mul_cancel X, rpow_one] },
  replace h : periodic (λ i, (a i + q)⁻¹) n := λ i, by simp only []; rw h,
  rw [ht, extra.periodic_sum_const h, hs, nsmul_eq_mul, mul_rpow, nsmul_eq_mul,
      mul_mul_mul_comm, ← rpow_nat_cast, nat.cast_two, bit1, rpow_add, rpow_one],
  rw nat.cast_ne_zero; exact ne_of_gt hn
end

variables {p : ℝ≥0} (hp : (range n).sum a = n • p)
include hp

private lemma case_q_le_p_step1 (c : ℝ≥0) :
  c ^ 2 * q * s + 2 * c * t ≤ p + q + c ^ 2 :=
begin
  sorry
end


/-
private lemma cauchy_schwarz_step1 : q * s + t ^ 2 / (p + q) ≤ 1 :=
begin
  replace hn : 0 < (n : ℝ≥0) := nat.cast_pos.mpr hn,
  suffices : q * (n • s) + (n • t) ^ 2 / (range n).sum (λ i, a i + q) ≤ n • 1,
    rwa [nsmul_eq_mul, sum_add_distrib, sum_const, card_range, hp, ← nsmul_add,
      nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, mul_pow, sq, mul_assoc, mul_left_comm,
      mul_div_mul_left _ _ (ne_of_gt hn), ← mul_div, ← mul_add, mul_le_mul_left hn] at this,
  have X : ∀ i, 0 < a i + q := λ i, add_pos_of_nonneg_of_pos (zero_le (a i)) hq,
  rw ← ht; refine le_of_le_of_eq (add_le_add_left (cauchy_schwarz_engel X n) _) _,
  nth_rewrite 2 ← card_range n,
  rw [← hs, mul_sum, ← sum_add_distrib, ← sum_const],
  refine sum_congr rfl (λ i _, _),
  rw [sq_sqrt, ← div_eq_mul_inv, ← add_div, add_comm, div_self (ne_of_gt (X i))]
end

private lemma cauchy_schwarz_step2 : t ^ 2 * s ≤ p / (p + q) :=
begin
  sorry
end

private lemma special_ineq_step1 : 
-/

end upper_bound



/-
section construction

private def good_seq (u v : ℝ≥0) (n : ℕ) : ℝ≥0 := ite (even n) u v

private lemma good_seq_periodic (u v : ℝ≥0) (n : ℕ) : periodic (good_seq u v) (2 * n) :=
  λ x, by simp only [good_seq, nat.even_add, two_mul, iff_self, iff_true]

private lemma good_seq_two_mul (u v : ℝ≥0) (n : ℕ) : good_seq u v (2 * n) = u :=
  by rw [good_seq, if_pos (even.mul_right even_two n)]

private lemma good_seq_two_mul_add_one (u v : ℝ≥0) (n : ℕ) : good_seq u v (2 * n + 1) = v :=
  by simp only [good_seq, nat.even_add_one, if_false, even.mul_right even_two n, not_true]

private lemma good_seq_sum (u v : ℝ≥0) (n : ℕ) : (range (2 * n)).sum (good_seq u v) = n * (u + v) :=
begin
  induction n with n n_ih,
  rw [mul_zero, sum_range_zero, nat.cast_zero, zero_mul],
  rw [nat.mul_succ, finset.sum_range_add, n_ih, nat.cast_succ, sum_range_succ,
      sum_range_one, add_zero, good_seq_two_mul, good_seq_two_mul_add_one, ← add_one_mul]
end

private lemma good_seq_target_sum (q u v : ℝ≥0) (n : ℕ) :
  target_sum q (good_seq u v) n =
    n * ((u / (v + q)) ^ (3⁻¹ : ℝ) + (v / (u + q)) ^ (3⁻¹ : ℝ)) :=
begin
  unfold target_sum; induction n with n n_ih,
  rw [mul_zero, sum_range_zero, nat.cast_zero, zero_mul],
  rw [nat.mul_succ, finset.sum_range_add, n_ih, nat.cast_succ, sum_range_succ,
      sum_range_one, add_zero, good_seq_two_mul, good_seq_two_mul_add_one,
      add_assoc, ← mul_add_one, good_seq_two_mul, ← add_one_mul]
end

end construction
-/



/-- Final solution, case `p ≤ q` -/
theorem final_solution_case_p_le_q {q p : ℝ≥0} (hq : 0 < q) (h : p ≤ q) (n : ℕ) :
  is_greatest ((λ a : ℕ → ℝ≥0, target_sum q a n) ''
    {a | (range n).sum a = n • p ∧ periodic a n})
  (n • (p / (p + q)) ^ (3⁻¹ : ℝ)) :=
begin
  sorry
end

/-- Final solution, case `q ≤ p` -/
theorem final_solution_case_q_le_p {q p : ℝ≥0} (hq : 0 < q) (h : q ≤ p) (n : ℕ) :
  is_greatest ((λ a : ℕ → ℝ≥0, target_sum q a n) ''
    {a | (range (2 * n)).sum a = (2 * n) • p ∧ periodic a (2 * n)})
  ((2 * n) • ((p + q) / (4 * q)) ^ (3⁻¹ : ℝ)) :=
begin
  sorry
end

end IMO2018A7
end IMOSL
