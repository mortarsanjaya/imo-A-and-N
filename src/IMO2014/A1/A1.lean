import algebra.big_operators.basic

/-! # IMO 2014 A1 (P1) -/

namespace IMOSL
namespace IMO2014A1

open finset

def d (z : ℕ → ℤ) (n : ℕ) := (range $ n + 1).sum z - n * z n

lemma d_zero (z : ℕ → ℤ) : d z 0 = z 0 :=
  by rw [d, sum_range_one, nat.cast_zero, zero_mul, sub_zero]

lemma d_succ (z : ℕ → ℤ) (n : ℕ) : d z (n + 1) = (range $ n + 1).sum z - n * z (n + 1) :=
  by rw [d, sum_range_succ _ (n + 1), add_sub_assoc, ← one_sub_mul,
    nat.cast_succ, ← sub_sub, sub_sub_cancel_left, neg_mul, ← sub_eq_add_neg]

lemma d_one (z : ℕ → ℤ) : d z 1 = z 0 :=
  by rw [d, sum_range_succ, sum_range_one, nat.cast_one, one_mul, add_sub_cancel]



variables {z : ℕ → ℤ} (h : strict_mono z)
include h

lemma main_lemma (n : ℕ) : d z (n + 1) ≤ d z n - n :=
  by rw [d_succ, d, sub_sub, sub_le_sub_iff_left, ← mul_add_one];
  exact mul_le_mul_of_nonneg_left (int.add_one_le_iff.mpr $ h n.lt_succ_self) n.cast_nonneg

lemma binom_bound : ∀ n, d z n ≤ z 0 - n.choose 2
| 0 := by rw [d_zero, nat.choose_zero_succ, nat.cast_zero, sub_zero]
| (n+1) := (main_lemma h n).trans $ by rw [nat.choose, nat.choose_one_right,
    sub_le_iff_le_add, sub_add, nat.cast_add, add_sub_cancel']; exact binom_bound n

lemma d_nonpos_of_big {n : ℕ} (h0 : (z 0).nat_abs ≤ n.choose 2) : d z n ≤ 0 :=
  (binom_bound h n).trans $ int.sub_nonpos_of_le $ (le_abs_self _).trans $
    by rwa [← int.coe_nat_abs, int.coe_nat_le]

lemma d_nonpos_mono {n : ℕ} (h0 : d z n ≤ 0) {k : ℕ} (h1 : n ≤ k) : d z k ≤ 0 :=
  nat.le_induction h0 (λ x _ h2, (main_lemma h x).trans $
    int.sub_nonpos_of_le $ h2.trans x.cast_nonneg) k h1

lemma d_one_pos (h0 : 0 < z 0) : 0 < d z 1 :=
  lt_of_lt_of_eq h0 (d_one z).symm





/-- The desired unique `N` -/
def greatest_d_pos : ℕ := nat.find_greatest (λ n, 0 < d z n) (z 0).nat_abs.succ

variables (h0 : 0 < z 0)
include h0

lemma greatest_d_pos_is_d_pos : 0 < d z (greatest_d_pos h) :=
  let P := λ n, 0 < d z n, h2 : P 1 := d_one_pos h h0 in
  nat.find_greatest_spec (nat.succ_pos _) h2

lemma greatest_d_pos_succ_not_d_pos : d z (greatest_d_pos h + 1) ≤ 0 :=
  le_of_not_lt $ nat.find_greatest_is_greatest (greatest_d_pos h).lt_succ_self $
    (le_iff_lt_or_eq.mp $ nat.find_greatest_le _).resolve_right $
    λ h1, not_le_of_lt (greatest_d_pos_is_d_pos h h0) $ d_nonpos_of_big h $
    by rw [greatest_d_pos, h1, nat.choose, nat.choose_one_right]; exact le_self_add

lemma eq_greatest_d_pos_iff {N : ℕ} : N = greatest_d_pos h ↔ 0 < d z N ∧ d z (N + 1) ≤ 0 :=
  ⟨λ h1, by rw h1; exact
    ⟨greatest_d_pos_is_d_pos h h0,
    greatest_d_pos_succ_not_d_pos h h0⟩,
  λ h1, le_antisymm
    (le_of_not_lt $ λ h2, not_le_of_lt h1.1 $
      d_nonpos_mono h (greatest_d_pos_succ_not_d_pos h h0) h2)
    (le_of_not_lt $ λ h2, not_le_of_lt (greatest_d_pos_is_d_pos h h0) $
      d_nonpos_mono h h1.2 h2)⟩



/-- Final solution, part 1: `N` is positive. -/
theorem final_solution_part1 : 0 < greatest_d_pos h :=
  nat.pos_of_ne_zero $ λ h1, nat.find_greatest_eq_zero_iff.mp
    h1 nat.one_pos (nat.succ_pos _) (d_one_pos h h0)

/-- Final solution, part 2: `N` is indeed the index we are looking for. -/
theorem final_solution_part2 {N : ℕ} : N = greatest_d_pos h ↔
  (↑N * z N < (range $ N + 1).sum z ∧ (range $ N + 1).sum z ≤ N * z (N + 1)) :=
  by rw [← sub_pos, ← d, ← sub_nonpos, ← d_succ]; exact eq_greatest_d_pos_iff h h0

/-- Final solution, extra: `C(N, 2) < z_0`, implemented as `C(N, 2) < (z 0).nat_abs`. -/
theorem final_solution_extra : (greatest_d_pos h).choose 2 < (z 0).nat_abs :=
  lt_of_not_le $ λ h1, not_lt_of_le (d_nonpos_of_big h h1) (greatest_d_pos_is_d_pos h h0)

end IMO2014A1
end IMOSL
