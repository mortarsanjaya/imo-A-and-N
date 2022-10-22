import data.real.sqrt tactic.fin_cases

/-! # IMO 2020 A3 -/

namespace IMOSL
namespace IMO2020A3

open real

private lemma AM_GM_sqrt {a b : ℝ} (h : 0 ≤ a) (h0 : 0 ≤ b) : 2 * sqrt (a * b) ≤ a + b :=
begin
  have h1 := two_mul_le_add_sq (sqrt a) (sqrt b),
  rwa [sq_sqrt h, sq_sqrt h0, mul_assoc, ← sqrt_mul h] at h1
end



/-- Final solution -/
theorem final_solution :
  is_least
    ((λ x : fin 4 → ℝ, x 0 / x 1 + x 1 / x 2 + x 2 / x 3 + x 3 / x 0) ''
      {x | (∀ i : fin 4, 0 < x i) ∧ (x 0 + x 2) * (x 1 + x 3) = x 0 * x 2 + x 1 * x 3})
    8 :=
begin
  refine ⟨_, λ a h, _⟩,
  { obtain ⟨c, h, h0⟩ : ∃ c : ℝ, 0 < c ∧ c + 1 / c = 4 :=
    begin
      have X : 0 < 2 + sqrt 3 := add_pos_of_pos_of_nonneg two_pos (sqrt_nonneg 3),
      refine ⟨2 + sqrt 3, X, _⟩,
      rw [add_div' _ _ _ (ne_of_gt X), div_eq_iff (ne_of_gt X),
          ← sq, add_sq, sq_sqrt, add_assoc, sq, two_mul],
      change (4 + 4 * sqrt 3 + (2 + 1 + 1) = _),
      rw [add_assoc (2 : ℝ), add_right_comm, ← bit0, ← bit0, ← mul_two, ← mul_add],
      norm_num
    end,
    have h1 : c ≠ 0 := ne_of_gt h,
    refine ⟨![c, 1, c, 1], ⟨λ i, _, _⟩, _⟩,
    fin_cases i; simp; assumption,
    simp; rw [← mul_two, ← bit0, mul_assoc, ← div_left_inj' h1, add_div,
      mul_div_cancel_left _ h1, mul_div_cancel_left _ h1, h0, two_mul, ← bit0],
    simp; rw [inv_eq_one_div, add_assoc, h0, ← bit0] },
  { rcases h with ⟨x, ⟨h, h0⟩, rfl⟩; simp only [],
    rw [add_assoc, add_add_add_comm],
    have Y : ∀ i j, 0 ≤ x i / x j := λ i j, le_of_lt (div_pos (h i) (h j)),
    refine le_trans _ (add_le_add (AM_GM_sqrt (Y 0 1) (Y 2 3)) (AM_GM_sqrt (Y 1 2) (Y 3 0))),
    rw [← mul_add, bit0, ← two_mul, mul_le_mul_left, div_mul_div_comm, div_mul_div_comm],
    replace Y : ∀ i j, 0 ≤ x i * x j := λ i j, le_of_lt (mul_pos (h i) (h j)),
    have Z : ∀ i j, sqrt (x i * x j) ≠ 0 := λ i j, sqrt_ne_zero'.mpr (mul_pos (h i) (h j)),
    rw [sqrt_div (Y 0 2), sqrt_div (Y 1 3), mul_comm (x 2), div_add_div _ _ (Z 1 3) (Z 0 2),
        ← sq, sq_sqrt (Y 0 2), ← sq, sq_sqrt (Y 1 3), ← h0, mul_comm, le_div_iff, bit0,
        ← two_mul, mul_mul_mul_comm],
    clear Y Z; have Y : ∀ i, 0 ≤ x i := λ i, le_of_lt (h i),
    refine mul_le_mul _ _ (mul_nonneg zero_le_two (sqrt_nonneg _)) (add_nonneg (Y _) (Y _));
      exact AM_GM_sqrt (Y _) (Y _),
    apply mul_pos; rw sqrt_pos; apply mul_pos; exact h _,
    exact two_pos }
end

end IMO2020A3
end IMOSL
