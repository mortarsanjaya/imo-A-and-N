import analysis.mean_inequalities extra.periodic.big_operators extra.real_prop.real_quadratic_sol

/-! # IMO 2018 A7 -/

namespace IMOSL
namespace IMO2018A7

open finset nnreal function
open_locale nnreal

noncomputable def target_sum (q : ℝ≥0) (a : ℕ → ℝ≥0) (n : ℕ) :=
  (range (2 * n)).sum (λ i, (a i / (a (i + 1) + q)) ^ (3⁻¹ : ℝ))



section upper_bound

private lemma AM_GM3 (a b c : ℝ≥0) :
  (a * b * c) ^ (3⁻¹ : ℝ) ≤ 3⁻¹ * (a + b + c) :=
begin
  rw [mul_rpow, mul_rpow, mul_add, mul_add],
  change (3⁻¹ : ℝ) with ((3⁻¹ : ℝ≥0) : ℝ),
  apply nnreal.geom_mean_le_arith_mean3_weighted,
  rw [← two_mul, ← add_one_mul, ← bit1],
  exact mul_inv_cancel three_ne_zero
end

private lemma one_liner {q c : ℝ≥0} (hq : 0 < q) (hc : 0 < c) (a b : ℝ≥0) :
  (a / (b + q)) ^ (3⁻¹ : ℝ) ≤
    (c / q) ^ (3⁻¹ : ℝ) * 3⁻¹ * ((a + q) / c + a / (a + q) + q / (b + q)) :=
begin
  rw mul_assoc; convert mul_le_mul_of_nonneg_left (AM_GM3 _ _ _) (zero_le _),
  rw [← mul_rpow, ← mul_assoc, ← mul_assoc, mul_comm (_ / q), div_mul_div_cancel _ (ne_of_gt hc),
      mul_comm (_ / q), div_mul_div_cancel, div_mul_div_cancel _ (ne_of_gt hq)],
  rw ← zero_lt_iff; exact add_pos_of_nonneg_of_pos (zero_le a) hq
end

private lemma upper_bound_non_optimized {q c : ℝ≥0} (hq : 0 < q) (hc : 0 < c)
  {a : ℕ → ℝ≥0} {n : ℕ} (h : a n = a 0) :
  (range n).sum (λ i, (a i / (a (i + 1) + q)) ^ (3⁻¹ : ℝ)) ≤ 
    (c / q) ^ (3⁻¹ : ℝ) * 3⁻¹ * (((range n).sum a + n * q) / c + n) :=
begin
  refine le_of_le_of_eq (sum_le_sum (λ i _, one_liner hq hc _ _)) _,
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← finset.sum_div,
      sum_add_distrib, add_assoc, sum_const, card_range, nsmul_eq_mul],
  congr' 2,
  rw [← add_left_inj (q / (a 0 + q)), add_assoc, ← sum_range_succ' (λ i, q / (a i + q))],
  simp only [],
  rw [sum_range_succ, ← add_assoc, ← sum_add_distrib, h, add_left_inj],
  conv_lhs { congr, skip, funext,
    rw [← add_div, div_self (ne_of_gt (add_pos_of_nonneg_of_pos (zero_le _) hq))] },
  rw [sum_const, card_range, nsmul_one]
end

private lemma upper_bound {q p : ℝ≥0} (hq : 0 < q) (hqp : q ≤ p)
  {a : ℕ → ℝ≥0} {n : ℕ} (h : periodic a n) (h0 : (range n).sum a = n * p) :
  (range n).sum (λ i, (a i / (a (i + 1) + q)) ^ (3⁻¹ : ℝ)) ≤ 
    (n / 2) * (2 * (1 + p / q)) ^ (3⁻¹ : ℝ) :=
begin
  have X : 0 < p + q := add_pos (lt_of_lt_of_le hq hqp) hq,
  have X0 : a n = a 0 := by rw [← zero_add n, h],
  convert upper_bound_non_optimized hq (mul_pos two_pos X) X0 using 1; clear X0,
  rw [mul_comm, mul_assoc]; congr,
  rw [nnreal.add_div' _ _ _ (ne_of_gt hq), one_mul, add_comm, mul_div],
  rw [h0, ← mul_add, mul_div_mul_right _ _ (ne_of_gt X), nnreal.div_add' _ _ _ two_ne_zero,
      ← mul_one_add, add_comm, ← bit1, mul_div, mul_comm, mul_assoc, mul_inv_cancel, mul_one],
  exact three_ne_zero
end

end upper_bound



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



/-- Final solution -/
theorem final_solution {q p : ℝ≥0} (hq : 0 < q) (hqp : q ≤ p) (n : ℕ) :
  is_lub ((λ a : ℕ → ℝ≥0, target_sum q a n) '' {a | (range (2 * n)).sum a = (2 * n) * p ∧ periodic a (2 * n)})
    (n * (2 * (1 + p / q)) ^ (3⁻¹ : ℝ)) :=
begin
  refine ⟨λ a h, _, λ a h, h _⟩,
  { rcases h with ⟨a, ⟨h, h0⟩, rfl⟩,
    unfold target_sum; convert upper_bound hq hqp h0 _ using 2,
    rw [nat.cast_mul, nat.cast_two, mul_div_cancel_left],
    exact two_ne_zero,
    rw [h, nat.cast_mul, nat.cast_two] },

  clear h a; suffices : ∃ u v : ℝ≥0, u + v = 2 * p ∧ u * v = q ^ 2,
  { rcases this with ⟨u, v, h, h0⟩,
    refine ⟨good_seq u v, ⟨_, good_seq_periodic u v n⟩, _⟩,
    rw [good_seq_sum, h, mul_left_comm, mul_assoc],
    simp only [good_seq_target_sum]; congr,

    obtain ⟨x, rfl⟩ : ∃ x : ℝ≥0, x ^ 2 = u := ⟨sqrt u, by rw sq_sqrt⟩,
    obtain ⟨y, rfl⟩ : ∃ y : ℝ≥0, y ^ 2 = v := ⟨sqrt v, by rw sq_sqrt⟩,
    rw [← mul_pow, sq_eq_sq (zero_le (x * y)) (zero_le q)] at h0,
    rw [← add_left_inj (2 * x * y), ← add_sq', mul_assoc, ← mul_add, h0] at h,
    rw [one_add_div (ne_of_gt hq), add_comm q, mul_div, ← h, ← h0],
    clear hq hqp h h0 p q n,

    suffices : ∀ a b : ℝ≥0, (a ^ 2 / b) ^ (3⁻¹ : ℝ) = a / (a * b) ^ (3⁻¹ : ℝ),
      rw [this, this, this, sq, sq, ← mul_add, ← add_mul, add_comm y,
          mul_left_comm x, mul_comm y, mul_right_comm, mul_comm, ← add_div],
    clear x y; intros a b,
    have X : (3 : ℝ) ≠ 0 := three_ne_zero,
    rw [← rpow_eq_rpow_iff X, inv_eq_one_div, rpow_self_rpow_inv X,
        div_rpow, rpow_self_rpow_inv X, ← div_div],
    congr; rcases eq_or_ne a 0 with rfl | ha,
    rw [sq, zero_mul, div_zero],
    rw [eq_div_iff ha, ← pow_succ', ← rpow_nat_cast, ← bit1, nat.cast_bit1, nat.cast_one] },

  { let x := sqrt (p ^ 2 - q ^ 2),
    have hx : x ≤ p := by rw sqrt_le_iff; exact tsub_le_self,
    refine ⟨p + x, p - x, _, _⟩,
    rw [add_assoc, add_tsub_cancel_of_le hx, two_mul],
    rw [← nnreal.coe_eq, nnreal.coe_mul, nnreal.coe_add, nnreal.coe_sub hx, ← sq_sub_sq,
        ← nnreal.coe_pow, ← nnreal.coe_pow, sq_sqrt, nnreal.coe_sub, sub_sub_cancel],
    rwa [← sqrt_le_iff, sqrt_sq] }
end

end IMO2018A7
end IMOSL
