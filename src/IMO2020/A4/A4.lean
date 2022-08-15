import
  analysis.mean_inequalities
  analysis.special_functions.pow
  algebra.big_operators.ring
  tactic.polyrith

/-! # IMO 2020 A4 (P2), Generalized Version -/

namespace IMOSL
namespace IMO2020A4

open real finset

section extra

theorem sq_sum_lt_sum_sq {n : ℕ} (h : 2 ≤ n) {x : fin n → ℝ} (h0 : ∀ k : fin n, 0 < x k) :
  univ.sum (λ i, x i ^ 2) < univ.sum x ^ 2 :=
begin
  revert x h0; refine nat.le_induction _ _ n h; clear h n,
  { intros x h,
    rw [fin.sum_univ_two, fin.sum_univ_two, add_sq', lt_add_iff_pos_right],
    exact mul_pos (mul_pos two_pos (h 0)) (h 1) },
  { intros n hn h x h0,
    replace h := @h (λ k, x (fin.cast_succ k)) (λ k, h0 _),
    rw [fin.sum_univ_cast_succ, fin.sum_univ_cast_succ, add_sq'],
    refine lt_trans (add_lt_add_right h _) (lt_add_of_pos_right _ _),
    refine mul_pos (mul_pos two_pos (sum_pos (λ k _, h0 _) _)) (h0 _),
    rw [univ_nonempty_iff, ← fin.pos_iff_nonempty],
    exact lt_of_lt_of_le two_pos hn }
end

end extra



/-- Final solution -/
theorem final_solution {n : ℕ} (h : 2 ≤ n) {a : ℝ} (h0 : 0 < a) {x : fin n → ℝ}
  (h1 : ∀ k : fin n, 0 < x k) (h2 : ∀ k : fin n, x k ≤ a) (h3 : a + univ.sum x = 1) :
  (3 - 2 * a) * (a ^ a * univ.prod (λ k, x k ^ (x k))) < 1 :=
begin
  have h32a : 0 < 3 - 2 * a :=
  begin
    suffices : a ≤ 1,
      linarith only [this],
    rw [← h3, le_add_iff_nonneg_right],
    exact sum_nonneg' (λ k, le_of_lt (h1 k))
  end,
  cases lt_or_le a (1 / 2) with h4 h4,
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left _ (le_of_lt h32a)) (_ : _ * a < 1),

  -- If a < 1/2, then a^a ∏ x_k^{x_k} ≤ a
  { refine le_of_le_of_eq (mul_le_mul_of_nonneg_left _ _) (_ : _ * a ^ univ.sum x = a),
    rotate,
    exact le_of_lt (rpow_pos_of_pos h0 a),
    rw [← rpow_add h0, h3, rpow_one],
    rw real.rpow_sum_of_nonneg (le_of_lt h0) (λ k _, le_of_lt (h1 k)),
    apply prod_le_prod; rintros k -,
    exacts [le_of_lt (rpow_pos_of_pos (h1 k) (x k)),
            real.rpow_le_rpow (le_of_lt (h1 k)) (h2 k) (le_of_lt (h1 k))] },

  -- If a < 1/2, then (3 - 2a) a < 1
  { rw ← sub_pos,
    refine lt_of_lt_of_eq _ (by ring : (1 - a) * (1 - 2 * a) = _),
    apply mul_pos; linarith only [h4] },
  
  refine lt_of_lt_of_le (mul_lt_mul_of_pos_left _ h32a) (_ : _ * (a ^ 2 + (1 - a) ^ 2) ≤ 1),

  -- If a ≥ 1/2, then a^a ∏ x_k^{x_k} < a^2 + (1 - a)^2
  { set y : fin (n + 1) → ℝ := fin.cons a x with hy,
    rw [← fin.sum_cons, ← hy] at h3,
    have h5 : a ^ a * univ.prod (λ (k : fin n), x k ^ x k) = univ.prod (λ k, y k ^ y k) :=
      by simp only [y, fin.prod_univ_succ, fin.cons_zero, fin.cons_succ],
    rw h5,
    replace h5 : ∀ k : fin (n + 1), k ∈ (univ : finset (fin (n + 1))) → 0 ≤ y k :=
    begin
      rintros k -,
      rcases fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩,
      simp only [y, fin.cons_zero]; exact le_of_lt h0,
      simp only [y, fin.cons_succ]; exact le_of_lt (h1 j)
    end,
    refine lt_of_le_of_lt (real.geom_mean_le_arith_mean_weighted _ y y h5 h3 h5) _,
    conv_lhs { congr, skip, funext, rw [← sq, hy] },
    rw [fin.sum_univ_succ, fin.cons_zero, real.add_lt_add_iff_left],
    simp only [fin.cons_succ, finset.sum_congr],
    refine lt_of_lt_of_eq (sq_sum_lt_sum_sq h h1) _,
    rw [hy, fin.sum_cons, ← eq_sub_iff_add_eq'] at h3,
    rw ← h3 },

  -- If a ≥ 1/2, then (3 - 2a)(a^2 + (1 - a)^2) ≤ 1
  { rw ← sub_nonneg,
    refine le_of_le_of_eq _ (by ring : 2 * (a - 1) ^ 2 * (2 * a - 1) = _),
    exact mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _)) (by linarith [h4]) }
end

/-- Final solution, original version -/
theorem final_solution_original {a b c d : ℝ} (h : 0 < d) (h0 : d ≤ c) (h1 : c ≤ b) (h2 : b ≤ a)
  (h3 : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) < 1 :=
begin
  let x : fin 3 → ℝ := ![b, c, d],
  have ha : 0 < a := by linarith only [h, h0, h1, h2],
  have h4 : ∀ k : fin 3, 0 < x k :=
    λ k, by fin_cases k; simp [x]; linarith only [h, h0, h1],
  have h5 : ∀ k : fin 3, x k ≤ a :=
    λ k, by fin_cases k; simp [x]; linarith only [h0, h1, h2],
  have h6 : a + univ.sum (λ (k : fin 3), x k) = 1 :=
    by rw [fin.sum_univ_three, ← add_assoc, ← add_assoc, ← h3]; simp [x],
  refine lt_of_le_of_lt _ (final_solution (by norm_num) ha h4 h5 h6),
  rw [fin.prod_univ_three, mul_assoc (a ^ a), mul_assoc]; simp [x],
  refine mul_le_mul_of_nonneg_right _ _,
  linarith only [h3, h0, h1],
  refine mul_nonneg _ (mul_nonneg (mul_nonneg _ _) _),
  all_goals { apply real.rpow_nonneg_of_nonneg, linarith }
end

end IMO2020A4
end IMOSL
