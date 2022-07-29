import
  data.real.basic
  algebra.periodic
  algebra.big_operators.intervals
  algebra.group.defs
  data.nat.periodic

/-! # IMO 2018 A2 (P2) -/

open finset function
open_locale classical

namespace IMOSL
namespace IMO2018A2

def good (a : ℕ → ℝ) := ∀ i : ℕ, a i * a (i + 1) + 1 = a (i + 2)



section extra

lemma periodic_sum_const {M : Type*} [add_cancel_comm_monoid M] {a : ℕ → M} {n : ℕ}
  (h : periodic a n) (k : ℕ) : (range n).sum (λ m, a (m + k)) = (range n).sum a :=
begin
  induction k with k k_ih,
  simp only [add_zero],
  conv_lhs { congr, skip, funext, rw [nat.succ_eq_one_add, ← add_assoc] },
  rw [← k_ih, ← add_left_inj (a (n + k)), ← sum_range_succ,
      add_comm n, h, sum_range_succ', zero_add]
end

lemma sum_nonneg_eq_zero {M : Type*} [linear_ordered_add_comm_group M] {a : ℕ → M}
  (h : ∀ i : ℕ, 0 ≤ a i) {n : ℕ} (h0 : (range n).sum a = 0) {j : ℕ} (h1 : j < n) : a j = 0 :=
begin
  revert h1 j; induction n with n n_ih,
  intros j h1; exfalso; exact not_le_of_lt h1 j.zero_le,
  rw [sum_range_succ, add_eq_zero_iff_eq_neg] at h0,
  have h1 : 0 ≤ (range n).sum (λ (x : ℕ), a x) := sum_nonneg (λ i _, h i),
  rw [h0, neg_nonneg] at h1,
  replace h1 := le_antisymm h1 (h n),
  rw [h1, neg_zero] at h0,
  intros j h2,
  rw [nat.lt_succ_iff, le_iff_eq_or_lt] at h2,
  rcases h2 with rfl | h2,
  exacts [h1, n_ih h0 h2]
end

end extra



private lemma periodic_to_periodic3 {a : ℕ → ℝ} (h : good a)
  {n : ℕ} (h0 : 0 < n) (h1 : periodic a n) : periodic a 3 :=
begin
  have h2 : (range n).sum (λ i, 2 * a (i + 2) ^ 2 + (a (i + 3) - a i) ^ 2) =
    (range n).sum (λ i, a (i + 3) ^ 2 + a i ^ 2 + 2 * (a (i + 2) - a i)) :=
  begin
    apply congr_arg; funext i,
    rw [add_comm, sub_sq, ← add_sub_right_comm, ← add_sub_right_comm, add_sub_assoc,
        add_right_inj, mul_assoc, ← mul_sub, mul_right_inj' (two_ne_zero : (2 : ℝ) ≠ 0),
        sub_eq_sub_iff_sub_eq_sub, ← sub_one_mul, mul_comm, sq, ← sub_one_mul],
    dsimp only [good] at h,
    conv at h { find (_ = _) { rw ← eq_sub_iff_add_eq } },
    rw [← h, mul_assoc, bit0, ← add_assoc, h]
  end,
  repeat { rw sum_add_distrib at h2 },
  rw [← mul_sum, ← mul_sum] at h2,
  repeat { rw periodic_sum_const (periodic.comp h1 (λ x, x ^ 2)) at h2 },
  dsimp only [comp] at h2,
  rw [← two_mul, add_right_inj, sum_sub_distrib, periodic_sum_const h1, sub_self, mul_zero] at h2,
  intros i,
  replace h2 := sum_nonneg_eq_zero (λ i, sq_nonneg (a (i + 3) - a i)) h2 (i.mod_lt h0),
  rwa [pow_eq_zero_iff, periodic.map_mod_nat h1, ← periodic.map_mod_nat h1,
       nat.mod_add_mod, periodic.map_mod_nat h1, sub_eq_zero] at h2,
  exact two_pos
end









end IMO2018A2
end IMOSL
