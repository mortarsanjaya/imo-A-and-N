import data.real.nnreal algebra.big_operators.intervals extra.nonneg_semifield

/-! # IMO 2010 A3, Generalized Version -/

open finset function
open_locale nnreal

namespace IMOSL
namespace IMO2010A3

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
  set c := x (2 * n + 1) + x (2 * n + 2) with hc,
  rw ← hc; clear_value c; clear hc h n x,
  rw ← nnreal.coe_le_coe; rcases c with ⟨c, h⟩,
  simp only [one_div, nonneg.coe_add, nonneg.coe_one, nonneg.coe_inv,
             subtype.coe_mk, nonneg.mk_pow, nnreal.coe_bit0],
  refine le_of_sub_nonneg (le_of_le_of_eq (sq_nonneg (c - 2⁻¹)) _),
  rw [sub_sq, add_sub_right_comm, mul_right_comm, mul_inv_cancel (two_ne_zero : (2 : ℝ) ≠ 0),
      one_mul, sq (2 : ℝ)⁻¹, ← mul_inv, two_mul, ← bit0],
end



private noncomputable def good_sup_ex (j : ℕ) : ℝ≥0 := ite (j % 2 = 0) (1 / 2) 0

private lemma example_is_good (n : ℕ) : good good_sup_ex :=
begin
  intros j; dsimp only [good_sup_ex],
  rw nat.add_mod_right,
  cases eq_or_ne (j % 2) 0 with h h,
  rw [nat.add_mod, if_pos h, h, zero_add, nat.one_mod, nat.one_mod,
      if_neg nat.one_ne_zero, add_zero, add_halves],
  rw [if_neg h, add_zero, zero_add, nat.add_mod, nat.one_mod],
  replace h : j % 2 = 1 := (or_iff_right h).mp (nat.mod_two_eq_zero_or_one j),
  rw [h, if_pos (nat.mod_self 2), one_div, nnreal.inv_le two_ne_zero, mul_one],
  exact one_le_two
end

private lemma example_sum_is_bound (n : ℕ) : target_sum good_sup_ex n = (n : ℝ≥0) / 4 :=
begin
  induction n with n n_ih,
  rw [target_sum_zero, nat.cast_zero, zero_div],
  rw [target_sum_succ, nat.succ_eq_add_one, nat.cast_add,
      nat.cast_one, add_div, n_ih, add_right_inj],
  dsimp only [good_sup_ex],
  rw [nat.add_mod_right, nat.add_mod_right, nat.add_mod, nat.mul_mod_right, zero_add],
  simp only [nat.one_ne_zero, if_true, eq_self_iff_true, if_false, nat.one_mod],
  rw [mul_zero, add_zero, div_mul_div_comm, mul_one, two_mul, ← bit0]
end



end IMO2010A3
end IMOSL
