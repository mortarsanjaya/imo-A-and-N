import
  algebra.big_operators.intervals
  algebra.big_operators.ring
  analysis.mean_inequalities_pow
  data.real.basic

/-!
# IMO 2010 A2

Let a, b, c, and d be real numbers such that a + b + c + d = 6 and a^2 + b^2 + c^2 + d^2 = 12.
Prove that 36 ≤ 4(a^3 + b^3 + c^3 + d^3) - (a^4 + b^4 + c^4 + d^4) ≤ 48.

## Solution

See <http://www.imo-official.org/problems/IMO2010SL.pdf>.
We will follow the official Solution 1.
-/

open finset

namespace IMOSL
namespace IMO2010A2

def s1 (x : ℕ → ℝ) := (range 4).sum x
def s2 (x : ℕ → ℝ) := (range 4).sum (λ i, x i ^ 2)
def S (x : ℕ → ℝ) := 4 * (range 4).sum (λ i, x i ^ 3) - (range 4).sum (λ i, x i ^ 4)



namespace extra

lemma range_succ_add {β : Type*} [add_comm_group β] (f : ℕ → β) (n : ℕ) :
    (range (n + 1)).sum f = f n + (range n).sum f :=
  by rw [← sub_eq_iff_eq_add, sum_range_succ_sub_sum]

/-- QM-AM inequality -/
theorem QM_AM (x : ℕ → ℝ) (n : ℕ) :
  (range n).sum x ^ 2 ≤ n * (range n).sum (λ i, x i ^ 2) :=
begin
  rcases nat.eq_zero_or_pos n with rfl | h,
  rw [range_zero, sum_empty, sum_empty, zero_pow zero_lt_two, mul_zero],
  have h0 :=
    real.pow_arith_mean_le_arith_mean_pow_of_even (range n) (λ _, (n : ℝ)⁻¹) x _ _ (even_two),
  simp only [] at h0,
  have h1 : 0 < (n : ℝ) := by rwa nat.cast_pos,
  have h2 : 0 < (n : ℝ)⁻¹ := by rwa inv_pos,
  rwa [← mul_sum, ← mul_sum, mul_pow, sq, mul_assoc, mul_le_mul_left h2, inv_mul_le_iff h1] at h0,
  simp only []; rintros - -,
  rwa inv_nonneg; exact nat.cast_nonneg n,
  simp only []; rw [sum_const, nsmul_eq_mul, card_range, mul_inv_cancel],
  apply ne_of_gt,
  rwa nat.cast_pos
end

theorem sq_sum_le_sum_sq (x : ℕ → ℝ) (h : ∀ n : ℕ, 0 ≤ x n) (n : ℕ) :
  (range n).sum (λ i, x i ^ 2) ≤ (range n).sum x ^ 2 :=
begin
  induction n with n n_ih,
  rw [range_zero, sum_empty, sum_empty, zero_pow zero_lt_two],
  rw [nat.succ_eq_add_one, range_succ_add, range_succ_add],
  refine le_trans (add_le_add_left n_ih _) (pow_add_pow_le (h n) (sum_nonneg' h) two_ne_zero),
end

end extra



namespace results

def T (x : ℕ → ℝ) := (range 4).sum (λ i, ((x i - 1) ^ 2) ^ 2)
def B (x : ℕ → ℝ) := 6 * s2 x - 4 * s1 x + 4
def C (x : ℕ → ℝ) := s2 x - 2 * s1 x + 4

lemma lem1 (x : ℕ → ℝ) : S x = B x - T x :=
begin
  rw eq_sub_iff_add_eq,
  dsimp only [S, s1, s2, T, B],
  have h : (λ i, 4 * x i ^ 3 - x i ^ 4 + ((x i - 1) ^ 2) ^ 2) = (λ i, 6 * x i ^ 2 - 4 * x i + 1) :=
    by funext i; ring,
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib, h, sum_add_distrib, sum_const,
      card_range, sum_sub_distrib, ← mul_sum, ← mul_sum, nat.smul_one_eq_coe],
  simp only [nat.cast_bit0, nat.cast_one]
end

lemma lem2 (x : ℕ → ℝ) : (range 4).sum (λ i, ((x i - 1) ^ 2)) = C x :=
begin
  simp only [sub_sq, one_pow, mul_one, sum_add_distrib, sum_sub_distrib, s2, s1, C],
  rw [sum_const, card_range, ← mul_sum, nat.smul_one_eq_coe],
  simp only [nat.cast_bit0, nat.cast_one],
end

lemma lem3 (x : ℕ → ℝ) : B x - C x ^ 2 ≤ S x ∧ S x ≤ B x - C x ^ 2 / 4 :=
begin
  rw lem1; split,
  { rw [sub_le_sub_iff_left, ← lem2],
    apply extra.sq_sum_le_sum_sq,
    intros n; exact sq_nonneg _ },
  { have h : (0 : ℝ) < ↑4 := by simp only [nat.cast_bit0, zero_lt_bit0, nat.cast_one, zero_lt_one],
    rw [sub_le_sub_iff_left, ← mul_le_mul_left h],
    refine le_of_eq_of_le _ (extra.QM_AM (λ i, (x i - 1) ^ 2) 4),
    simp only [nat.cast_bit0, nat.cast_one] at h ⊢,
    rw [← lem2, mul_div_cancel' _ (ne_of_gt h)] }
end

end results



/-- Final solution -/
theorem final_solution {x : ℕ → ℝ} (h : s1 x = 6) (h0 : s2 x = 12) : 36 ≤ S x ∧ S x ≤ 48 :=
begin
  have h1 := results.lem3 x,
  rw [results.B, results.C, h, h0] at h1,
  norm_num at h1,
  exact h1
end

end IMO2010A2
end IMOSL
