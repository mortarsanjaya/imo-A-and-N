import analysis.mean_inequalities extra.periodic.big_operators extra.real_prop.real_quadratic_sol

/-! # IMO 2018 A7 -/

namespace IMOSL
namespace IMO2018A7

open finset nnreal function
open_locale nnreal

noncomputable def target_sum (q : ℝ≥0) (a : ℕ → ℝ≥0) (n : ℕ) :=
  (range n).sum (λ i, (a i / (a (i + 1) + q)) ^ (3⁻¹ : ℝ))





section extra_lemmas

private lemma classical_cauchy_schwarz {α : Type*} (S : finset α) (a b : α → ℝ≥0) :
  S.sum (λ i, sqrt (a i * b i)) ^ 2 ≤ S.sum a * S.sum b :=
begin
  rw [← le_sqrt_iff, sqrt_eq_rpow, mul_rpow],
  convert nnreal.inner_le_Lp_mul_Lq
    S (λ i, sqrt (a i)) (λ i, sqrt (b i)) ⟨one_lt_two, add_halves' 1⟩,
  funext i; rw sqrt_mul,
  all_goals { funext i; rw [← nat.cast_two, rpow_nat_cast, sq_sqrt] }
end



private lemma special_ineq {q : ℝ≥0} (hq : 0 < q) (x c : ℝ≥0) :
  2 * c * sqrt x + c ^ 2 * q * (x + q)⁻¹ ≤ x + q + c ^ 2 :=
begin
  sorry
end

end extra_lemmas



section upper_bound

variables {a : ℕ → ℝ≥0} {n : ℕ} (hn : 0 < n) {q t r : ℝ≥0} (hq : 0 < q)
  (ht : (range n).sum (λ i, sqrt (a i)) = n • t) (hr : (range n).sum (λ i, (a i + q)⁻¹) = n • r)
include hn hq ht hr
  
private lemma holder_target (h : periodic a n) : target_sum q a n ≤ n • (t ^ 2 * r) ^ (3⁻¹ : ℝ) :=
begin
  have X : (3 / 2 : ℝ).is_conjugate_exponent 3 := by rw real.is_conjugate_exponent_iff; norm_num,
  unfold target_sum; convert nnreal.inner_le_Lp_mul_Lq (range n)
    (λ i, a i ^ (3⁻¹ : ℝ)) (λ i, (a (i + 1) + q)⁻¹ ^ (3⁻¹ : ℝ)) X,
  funext; rw [div_eq_mul_inv, mul_rpow],
  replace X : (3 : ℝ) ≠ 0 := three_ne_zero,
  rw [one_div_div, ← rpow_eq_rpow_iff X, nsmul_eq_mul, mul_rpow, ← rpow_mul, inv_mul_cancel X,
      rpow_one, mul_rpow, ← rpow_mul, div_mul_cancel 2 X, ← rpow_mul, div_mul_cancel 1 X, rpow_one],
  conv_rhs {
    congr, congr, congr, skip, funext, rw [← rpow_mul, mul_div, inv_mul_cancel X, ← sqrt_eq_rpow],
    skip, skip, congr, skip, funext, rw [← rpow_mul, inv_mul_cancel X, rpow_one] },
  replace h : periodic (λ i, (a i + q)⁻¹) n := λ i, by simp only []; rw h,
  rw [ht, extra.periodic_sum_const h, hr, nsmul_eq_mul, mul_rpow, nsmul_eq_mul,
      mul_mul_mul_comm, ← rpow_nat_cast, nat.cast_two, bit1, rpow_add, rpow_one],
  rw nat.cast_ne_zero; exact ne_of_gt hn
end

variables {p : ℝ≥0} (hp : (range n).sum a = n • p)
include hp

private lemma case_p_le_q_step1 : t ^ 2 + q * r * (p + q) ≤ p + q :=
begin
  replace hn : 0 < (n : ℝ≥0) := nat.cast_pos.mpr hn,
  rw [← mul_le_mul_left (pow_pos hn 2), mul_add, ← mul_pow, ← nsmul_eq_mul],
  have X : ∀ i : ℕ, a i + q ≠ 0 := λ i, ne_of_gt (add_pos_of_nonneg_of_pos ((zero_le (a i))) hq),
  suffices : (n • t) ^ 2 ≤ (range n).sum (λ i, a i / (a i + q)) * (n * (p + q)),
  { convert add_le_add_right this _,
    rw [← mul_assoc, ← mul_assoc, ← add_mul]; congr' 1,
    rw [mul_comm, sq, mul_assoc, ← mul_add]; congr' 1,
    rw [mul_left_comm, ← nsmul_eq_mul, ← hr, mul_sum, ← sum_add_distrib],
    conv_rhs { congr, skip, funext, rw [← div_eq_mul_inv, ← add_div, div_self (X x)] },
    rw [sum_const, nsmul_one, card_range] },
  rw ← ht; convert classical_cauchy_schwarz (range n) (λ i, a i / (a i + q)) (λ i, a i + q),
  funext i; rw div_mul_cancel _ (X i),
  rw [sum_add_distrib, hp, sum_const, card_range, ← nsmul_add, nsmul_eq_mul]
end

private lemma case_p_le_q_step2 (h : p ≤ q) : t ^ 2 * r ≤ p / (p + q) :=
begin
  rw [nnreal.le_div_iff (ne_of_gt (add_pos_of_nonneg_of_pos (zero_le p) hq)),
      ← mul_le_mul_left hq, mul_assoc, mul_left_comm, ← mul_assoc q, mul_comm q p],
  suffices h0 : t ^ 2 ≤ p,
  { have h1 := case_p_le_q_step1 hn hq ht hr hp,
    set c := q * r * (p + q) with hc,
    rw le_iff_exists_add at h0,
    rw ← hc; rcases h0 with ⟨a, rfl⟩,
    rw [add_assoc, add_le_add_iff_left] at h1,
    refine le_trans (mul_le_mul_left' h1 _) _,
    rw [add_comm, mul_add, add_mul, add_le_add_iff_left, mul_comm],
    exact mul_le_mul_left' (le_trans le_self_add h) a },
  replace hn : 0 < (n : ℝ≥0) := nat.cast_pos.mpr hn,
  rw [← mul_le_mul_left (pow_pos hn 2), ← mul_pow, ← nsmul_eq_mul,
      ← ht, sq (n : ℝ≥0), mul_assoc, ← nsmul_eq_mul n p, ← hp],
  convert classical_cauchy_schwarz (range n) (λ _, 1) a,
  funext i; rw one_mul,
  rw [sum_const, nsmul_one, card_range]
end


private lemma case_p_ge_q_step1 (c : ℝ≥0) : 2 * c * t + c ^ 2 * q * r ≤ p + q + c ^ 2 :=
begin
  replace hn : 0 < (n : ℝ≥0) := nat.cast_pos.mpr hn,
  rw [← mul_le_mul_left hn, mul_add, mul_left_comm, ← nsmul_eq_mul, ← ht,
      mul_left_comm, ← nsmul_eq_mul, ← hr, mul_sum, mul_sum, ← sum_add_distrib],
  refine le_of_le_of_eq (sum_le_sum (λ i _, special_ineq hq (a i) c)) _,
  rw [sum_add_distrib, sum_const, sum_add_distrib, sum_const,
      hp, card_range, ← smul_add, ← smul_add, ← nsmul_eq_mul]
end

private lemma case_p_ge_q_step2 : t ^ 2 * r ≤ (p + q) / (4 * q) :=
begin
  have X : (3 : ℝ≥0) ≠ 0 := by norm_num,
  have h : ∀ a b : ℝ≥0, 3 * (a ^ 2 * b) ^ (3⁻¹ : ℝ) ≤ 2 * a + b :=
  begin
    intros a b,
    rw [mul_le_iff_le_inv X, mul_comm (3⁻¹ : ℝ≥0), ← div_eq_mul_inv, add_div, mul_div_right_comm,
        div_eq_mul_one_div b, mul_comm b, mul_rpow, ← rpow_nat_cast, nat.cast_two, ← rpow_mul],
    convert geom_mean_le_arith_mean2_weighted _ _ _ _ _,
    rw [nonneg.coe_div, nnreal.coe_bit1, nnreal.coe_bit0, nnreal.coe_one, div_eq_mul_inv],
    rw [← inv_eq_one_div, nnreal.coe_inv, nnreal.coe_bit1, nnreal.coe_one],
    rw [← add_div, ← bit1, div_self X]
  end,

  replace h := h (sqrt (2 * (p + q)) * t) (sqrt (2 * (p + q)) ^ 2 * q * r),
  rw ← mul_assoc 2 (sqrt (2 * (p + q))) at h,
  replace h := le_trans h (case_p_ge_q_step1 hn hq ht hr hp _),
  rw [mul_pow, sq_sqrt, ← one_add_mul, add_comm (1 : ℝ≥0), ← bit1, mul_le_mul_left₀ X,
      inv_eq_one_div, rpow_one_div_le_iff zero_lt_three, mul_mul_mul_comm] at h,
  generalize_hyp h0 : p + q = d at h ⊢,
  generalize_hyp h1 : t ^ 2 * r = f at h ⊢,
  rw [← mul_assoc, ← sq, mul_comm 2 d, mul_pow, sq (2 : ℝ≥0), mul_two, ← bit0] at h,
  replace X : 0 < d := by rw ← h0; exact add_pos_of_nonneg_of_pos (zero_le p) hq,
  rwa [mul_assoc (d ^ 2), mul_assoc, bit1, rpow_add (ne_of_gt X), rpow_one, ← rpow_nat_cast,
       nat.cast_two, mul_le_mul_left (rpow_pos X), mul_comm, ← nnreal.le_div_iff] at h,
  exact mul_ne_zero four_ne_zero (ne_of_gt hq)
end

end upper_bound







/-- Final solution, case `p ≤ q` -/
theorem final_solution_case_p_le_q {q p : ℝ≥0} (hq : 0 < q) (h : p ≤ q) (n : ℕ) :
  is_greatest ((λ a : ℕ → ℝ≥0, target_sum q a n) ''
    {a | (range n).sum a = n • p ∧ periodic a n})
  (n • (p / (p + q)) ^ (3⁻¹ : ℝ)) :=
begin
  refine ⟨⟨λ _, p, ⟨by rw [sum_const, card_range], λ i, rfl⟩, _⟩, λ c h, _⟩,
  unfold target_sum; rw [sum_const, card_range],
  rcases h with ⟨a, ⟨h0, h1⟩, rfl⟩,
  rcases n.eq_zero_or_pos with rfl | hn,
  unfold target_sum; rw [sum_range_zero, zero_smul],
  have X : (n : ℝ≥0) ≠ 0 := ne_of_gt (nat.cast_pos.mpr hn),
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (range n).sum (λ i, sqrt (a i)) = n • t :=
    ⟨(range n).sum (λ i, sqrt (a i)) / n, by rw [nsmul_eq_mul, mul_div_cancel' _ X]⟩,
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (range n).sum (λ i, (a i + q)⁻¹) = n • r :=
    ⟨(range n).sum (λ i, (a i + q)⁻¹) / n, by rw [nsmul_eq_mul, mul_div_cancel' _ X]⟩,
  refine le_trans (holder_target hn hq ht hr h1) (smul_le_smul_of_nonneg _ n.zero_le),
  exact rpow_le_rpow (case_p_le_q_step2 hn hq ht hr h0 h) (inv_nonneg.mpr zero_le_three)
end

/-- Final solution, case `q ≤ p` -/
theorem final_solution_case_q_le_p {q p : ℝ≥0} (hq : 0 < q) (h : q ≤ p) (n : ℕ) :
  is_greatest ((λ a : ℕ → ℝ≥0, target_sum q a (2 * n)) ''
    {a | (range (2 * n)).sum a = (2 * n) • p ∧ periodic a (2 * n)})
  ((2 * n) • ((p + q) / (4 * q)) ^ (3⁻¹ : ℝ)) :=
begin
  refine ⟨_, λ c h, _⟩,
  { sorry

  },
  { rcases h with ⟨a, ⟨h0, h1⟩, rfl⟩,
    rcases n.eq_zero_or_pos with rfl | hn,
    unfold target_sum; rw [mul_zero, sum_range_zero, zero_smul],
    replace hn := mul_pos two_pos hn,
    have X : ((2 * n : ℕ) : ℝ≥0) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt hn),
    obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (range (2 * n)).sum (λ i, sqrt (a i)) = (2 * n) • t :=
      ⟨(range (2 * n)).sum (λ i, sqrt (a i)) / ↑(2 * n),
        by rw [nsmul_eq_mul, mul_div_cancel' _ X]⟩,
    obtain ⟨r, hr⟩ : ∃ r : ℝ≥0, (range (2 * n)).sum (λ i, (a i + q)⁻¹) = (2 * n) • r :=
      ⟨(range (2 * n)).sum (λ i, (a i + q)⁻¹) / ↑(2 * n),
        by rw [nsmul_eq_mul, mul_div_cancel' _ X]⟩,
    refine le_trans (holder_target hn hq ht hr h1) (smul_le_smul_of_nonneg _ (le_of_lt hn)),
    exact rpow_le_rpow (case_p_ge_q_step2 hn hq ht hr h0) (inv_nonneg.mpr zero_le_three) }
end

end IMO2018A7
end IMOSL
