import data.real.nnreal algebra.big_operators.intervals algebra.periodic

/-! # IMO 2010 A3 -/

namespace IMOSL
namespace IMO2010A3

open finset function
open_locale nnreal

def good (x : ℕ → ℝ≥0) := ∀ j : ℕ, x j + x (j + 1) + x (j + 2) ≤ 1
def target_sum (x : ℕ → ℝ≥0) (n : ℕ) := (range (2 * n)).sum (λ i, x i * x (i + 2))



private lemma lem1 {a b c d : ℝ≥0} (h : a + b + c ≤ 1) (h0 : b + c + d ≤ 1) :
  a * c + b * d ≤ 1 / 4 :=
begin
  ---- Letting `x = b + c`, reduce to `x ≤ x^2 + 1/4`
  rw add_assoc at h,
  generalize_hyp hx : b + c = x at h h0,
  rw [← add_le_add_iff_left (x * c), ← add_assoc, ← add_mul, add_comm x],
  refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_right h (zero_le _)) _) _,
  rw [one_mul, ← add_le_add_iff_right (b * x), add_assoc, ← mul_add, add_comm d],
  refine le_trans (add_le_add_left (mul_le_mul_of_nonneg_left h0 (zero_le _)) _) _,
  rw [mul_one, add_right_comm, mul_comm, ← add_mul, add_comm, hx, ← sq],
  clear h h0 hx a b c d,

  ---- Prove that `x ≤ x^2 + 1/4`
  rcases x with ⟨x, h⟩,
  rw [← nnreal.coe_le_coe, nonneg.coe_add, nonneg.mk_pow, subtype.coe_mk, subtype.coe_mk],
  convert two_mul_le_add_sq x (1 / 2),
  rw [mul_right_comm, mul_div_cancel' 1 (two_ne_zero : (2 : ℝ) ≠ 0), one_mul],
  norm_num
end

private lemma target_sum_good_bound {x : ℕ → ℝ≥0} (h : good x) (n : ℕ) :
  target_sum x n ≤ (n : ℝ≥0) / 4 :=
begin
  unfold target_sum; induction n with n n_ih,
  rw [mul_zero, sum_range_zero, nat.cast_zero, zero_div],
  rw [nat.mul_succ, sum_range_succ, sum_range_succ, add_assoc, nat.cast_succ, add_div],
  exact add_le_add n_ih (lem1 (h _) (h _))
end

private lemma bin_even_good : good (λ j, ite (even j) (1 / 2) 0) :=
begin
  intros j; simp only [nat.even_add_one, not_not],
  rw [ite_not, apply_ite2 has_add.add, add_zero, zero_add, apply_ite2 has_add.add,
      add_zero, ← add_div, ← bit0, div_self (two_ne_zero : (2 : ℝ≥0) ≠ 0)],
  by_cases h : even j,
  rw if_pos h,
  rw [if_neg h, one_div, nnreal.inv_le two_ne_zero, mul_one],
  exact one_le_two
end

private lemma bin_even_target_sum (n : ℕ) :
  target_sum (λ j, ite (even j) (1 / 2) 0) n = (n : ℝ≥0) / 4 :=
begin
  unfold target_sum; induction n with n n_ih,
  rw [mul_zero, sum_range_zero, nat.cast_zero, zero_div],
  rw [nat.mul_succ, sum_range_succ, sum_range_succ, n_ih, add_assoc, nat.cast_succ, add_div],
  simp only [nat.even_add_one, not_not, even.mul_right even_two]; simp only [not_true],
  rw [if_true, if_false, zero_mul, add_zero, one_div_mul_one_div, bit0, ← two_mul]
end



/-- Final solution -/
theorem final_solution (n : ℕ) :
  is_greatest ((λ x : ℕ → ℝ≥0, target_sum x n) '' {x | good x ∧ periodic x (2 * n)})
    ((n : ℝ≥0) / 4) :=
begin
  refine ⟨⟨_, ⟨bin_even_good, λ k, _⟩, bin_even_target_sum n⟩, λ a h, _⟩,
  simp only [nat.even_add, even_two_mul, iff_true],
  rcases h with ⟨x, ⟨h, -⟩, rfl⟩,
  exact target_sum_good_bound h n
end

end IMO2010A3
end IMOSL
