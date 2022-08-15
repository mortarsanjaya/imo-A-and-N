import
  algebra.big_operators.ring
  analysis.mean_inequalities_pow

/-! # IMO 2010 A2 -/

open finset

namespace IMOSL
namespace IMO2010A2

def s1 {n : ℕ} (x : fin n → ℝ) := univ.sum x
def s2 {n : ℕ} (x : fin n → ℝ) := univ.sum (λ i, x i ^ 2)
def S {n : ℕ} (x : fin n → ℝ) := 4 * univ.sum (λ i, x i ^ 3) - univ.sum (λ i, x i ^ 4)



namespace extra

/-- QM-AM inequality -/
theorem QM_AM {n : ℕ} (x : fin n → ℝ) : univ.sum x ^ 2 ≤ n * univ.sum (λ i, x i ^ 2) :=
begin
  rcases nat.eq_zero_or_pos n with rfl | h,
  rw [fin.sum_univ_zero, fin.sum_univ_zero, zero_pow two_pos, mul_zero],
  have h0 := real.pow_arith_mean_le_arith_mean_pow_of_even univ (λ _, (n : ℝ)⁻¹) x _ _ (even_two),
  simp only [] at h0,
  have h1 : 0 < (n : ℝ) := by rwa nat.cast_pos,
  have h2 : 0 < (n : ℝ)⁻¹ := by rwa inv_pos,
  rwa [← mul_sum, ← mul_sum, mul_pow, sq, mul_assoc, mul_le_mul_left h2, inv_mul_le_iff h1] at h0,
  simp only []; rintros - -,
  rwa inv_nonneg; exact nat.cast_nonneg n,
  simp only []; rw [sum_const, nsmul_eq_mul, card_univ, fintype.card_fin, mul_inv_cancel],
  apply ne_of_gt,
  rwa nat.cast_pos
end

theorem sq_sum_le_sum_sq {n : ℕ} (x : fin n → ℝ) (h : ∀ k : fin n, 0 ≤ x k) :
  univ.sum (λ i, x i ^ 2) ≤ univ.sum x ^ 2 :=
begin
  induction n with n n_ih,
  rw [fin.sum_univ_zero, fin.sum_univ_zero, zero_pow two_pos],
  rw [fin.sum_univ_cast_succ, fin.sum_univ_cast_succ, add_sq'],
  refine le_trans (add_le_add_right (n_ih _ _) _) (le_add_of_nonneg_right _),
  intros k; exact h _,
  exact mul_nonneg (mul_nonneg zero_le_two (sum_nonneg' (λ i, h _))) (h _)
end

end extra



section results

variables {n : ℕ} (x : fin n → ℝ)

private def T := univ.sum (λ i, ((x i - 1) ^ 2) ^ 2)
private def B := 6 * s2 x - 4 * s1 x + n
private def C := s2 x - 2 * s1 x + n

private lemma lem1 : S x = B x - T x :=
begin
  rw eq_sub_iff_add_eq,
  dsimp only [S, s1, s2, T, B],
  have h : (λ i, 4 * x i ^ 3 - x i ^ 4 + ((x i - 1) ^ 2) ^ 2) = (λ i, 6 * x i ^ 2 - 4 * x i + 1) :=
    by funext i; ring,
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib, h, sum_add_distrib, sum_const, card_univ,
      fintype.card_fin, sum_sub_distrib, ← mul_sum, ← mul_sum, nat.smul_one_eq_coe],
end

private lemma lem2 : univ.sum (λ i, ((x i - 1) ^ 2)) = C x :=
begin
  simp only [sub_sq, one_pow, mul_one, sum_add_distrib, sum_sub_distrib, s2, s1, C],
  rw [sum_const, card_univ, fintype.card_fin, ← mul_sum, nat.smul_one_eq_coe]
end

private lemma lem3 (h : 0 < n) : B x - C x ^ 2 ≤ S x ∧ S x ≤ B x - C x ^ 2 / n :=
begin
  rw lem1; split,
  { rw [sub_le_sub_iff_left, ← lem2],
    apply extra.sq_sum_le_sum_sq,
    intros n; exact sq_nonneg _ },
  { replace h : (0 : ℝ) < n := nat.cast_pos.mpr h,
    rw [sub_le_sub_iff_left, ← mul_le_mul_left h],
    refine le_of_eq_of_le _ (extra.QM_AM (λ i, (x i - 1) ^ 2)),
    rw [← lem2, mul_div_cancel' _ (ne_of_gt h)] }
end

end results



/-- Final solution -/
theorem final_solution {x : fin 4 → ℝ} (h : s1 x = 6) (h0 : s2 x = 12) : 36 ≤ S x ∧ S x ≤ 48 :=
  by convert lem3 x zero_lt_four; rw [B, C, h, h0]; norm_num

end IMO2010A2
end IMOSL
