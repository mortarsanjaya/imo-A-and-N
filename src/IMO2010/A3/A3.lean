import data.real.nnreal algebra.big_operators.intervals algebra.periodic extra.nonneg_semifield

/-! # IMO 2010 A3, Generalized Version -/

namespace IMOSL
namespace IMO2010A3

open finset function
open_locale nnreal

def good (x : ℕ → ℝ≥0) := ∀ j : ℕ, x j + x (j + 1) + x (j + 2) ≤ 1



section extra

noncomputable def target_sum (x : ℕ → ℝ≥0) (n : ℕ) := (range (2 * n)).sum (λ i, x i * x (i + 2))

private lemma target_sum_zero (x : ℕ → ℝ≥0) : target_sum x 0 = 0 :=
  by rw [target_sum, mul_zero, range_zero, sum_empty]

private lemma target_sum_succ (x : ℕ → ℝ≥0) (n : ℕ) : target_sum x n.succ =
    target_sum x n + (x (2 * n) * x (2 * n + 2) + x (2 * n + 1) * x (2 * n + 1 + 2)) :=
  by rw [target_sum, target_sum, nat.succ_eq_add_one, mul_add_one,
    finset.sum_range_add, sum_range_succ, sum_range_one, add_zero]

end extra



/-- Upper bound on the target sum over all good sequences -/
private lemma good_up_bound {x : ℕ → ℝ≥0} (h : good x) (n : ℕ) : target_sum x n ≤ (n : ℝ≥0) / 4 :=
begin
  induction n with n n_ih,
  rw [target_sum_zero, nat.cast_zero, zero_div],
  rw [target_sum_succ, nat.succ_eq_add_one, nat.cast_add, nat.cast_one, add_div],
  apply add_le_add n_ih; clear n_ih,
  rw [← add_le_add_iff_left ((x (2 * n + 1) + x (2 * n + 2)) * x (2 * n + 2)),
      ← add_assoc, ← add_mul, add_comm _ (x (2 * n)), ← add_assoc],
  refine le_trans (add_le_add_right (mul_le_mul_of_nonneg_right (h _) (zero_le _)) _) _,
  rw [← add_le_add_iff_right (x (2 * n + 1) * (x (2 * n + 1) + x (2 * n + 1 + 1))),
      one_mul, add_assoc, ← mul_add, add_comm (x (2 * n + 1 + 2))],
  refine le_trans (add_le_add_left (mul_le_mul_of_nonneg_left (h _) (zero_le _)) _) _,
  rw [mul_one, add_right_comm, mul_comm _ (x _), add_assoc _ 1, ← add_mul, add_comm, ← sq],
  generalize : x (2 * n + 1) + x (2 * n + 2) = c,
  rcases c with ⟨c, h⟩,
  rw [← nnreal.coe_le_coe, nonneg.coe_add, nonneg.mk_pow, subtype.coe_mk, subtype.coe_mk,
      nonneg.coe_div, nnreal.coe_bit0, nnreal.coe_bit0, nonneg.coe_one, one_div, ← sub_nonneg],
  convert (sq_nonneg (c - 2⁻¹)),
  rw [sub_sq', mul_right_comm, mul_inv_cancel, one_mul, sq (2 : ℝ)⁻¹, ← mul_inv, two_mul, ← bit0],
  exact two_ne_zero
end



private noncomputable def good_sup (j : ℕ) : ℝ≥0 := ite (even j) (1 / 2) 0

private lemma good_sup1 : good good_sup :=
begin
  intros j; simp only [good_sup, nat.even_add_one, not_not],
  rw [ite_not, apply_ite2 has_add.add, add_zero, zero_add, apply_ite2 has_add.add,
      add_zero, ← add_div, ← bit0, div_self (two_ne_zero : (2 : ℝ≥0) ≠ 0)],
  by_cases h : even j,
  rw if_pos h,
  rw [if_neg h, one_div, nnreal.inv_le two_ne_zero, mul_one],
  exact one_le_two
end

private lemma good_sup2 (n : ℕ) : target_sum good_sup n = (n : ℝ≥0) / 4 :=
begin
  induction n with n n_ih,
  rw [target_sum_zero, nat.cast_zero, zero_div],
  rw [target_sum_succ, nat.succ_eq_add_one, nat.cast_add, nat.cast_one, add_div, n_ih],
  simp only [good_sup, nat.even_add_one, not_not, add_right_inj],
  rw [ite_not, apply_ite2 has_mul.mul, apply_ite2 has_mul.mul, apply_ite2 has_add.add,
      mul_zero, add_zero, zero_add, if_t_t, ← mul_div_mul_comm, mul_one, two_mul, ← bit0]
end

private lemma good_sup3 (n : ℕ) : periodic good_sup (2 * n) :=
  λ x, by simp only [good_sup, nat.even_add, two_mul, iff_self, iff_true]



/-- Final solution -/
theorem final_solution (n : ℕ) : is_lub ((λ x : ℕ → ℝ≥0, target_sum x n) ''
  {x | good x ∧ periodic x (2 * n)}) ((n : ℝ≥0) / 4) :=
begin
  refine ⟨λ a h, _, λ a h, h ⟨good_sup, ⟨good_sup1, good_sup3 n⟩, good_sup2 n⟩⟩,
  rcases h with ⟨x, ⟨h, -⟩, rfl⟩,
  exact good_up_bound h n
end

end IMO2010A3
end IMOSL
