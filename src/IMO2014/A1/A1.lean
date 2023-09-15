import algebra.big_operators.basic

/-! # IMO 2014 A1 (P1) -/

namespace IMOSL
namespace IMO2014A1

open finset

def d (z : ℕ → ℤ) (n : ℕ) := (range (n + 1)).sum z - n * z n

lemma d_zero (z : ℕ → ℤ) : d z 0 = z 0 :=
  (congr_arg2 _ (sum_range_one z) (z 0).zero_mul).trans $ sub_zero (z 0)

lemma d_succ (z : ℕ → ℤ) (n : ℕ) : d z (n + 1) = (range (n + 1)).sum z - n * z (n + 1) :=
  (congr_arg2 _ (sum_range_succ z _) (add_one_mul (n : ℤ) _)).trans $
    add_sub_add_right_eq_sub _ _ _

lemma d_one (z : ℕ → ℤ) : d z 1 = z 0 :=
  (d_succ z 0).trans $ (congr_arg2 _ (sum_range_one z) (z 1).zero_mul).trans $ sub_zero (z 0)



variables {z : ℕ → ℤ} (h : strict_mono z)
include h

lemma main_lemma (n : ℕ) : d z (n + 1) ≤ d z n - n :=
  (d_succ z n).trans_le $ (sub_sub _ _ _).ge.trans' $ sub_le_sub_left
    ((mul_add_one _ _).symm.trans_le $ mul_le_mul_of_nonneg_left
      (int.add_one_le_iff.mpr $ h n.lt_succ_self) n.cast_nonneg) _

lemma binom_bound : ∀ n, d z n ≤ z 0 - n.choose 2
| 0 := ((d_zero z).trans (sub_zero _).symm).le
| (n+1) := (main_lemma h n).trans $ (sub_le_sub_right (binom_bound n) _).trans_eq $
    (sub_sub _ _ _).trans $ congr_arg2 _ rfl $ (int.coe_nat_add _ _).symm.trans $
    congr_arg _ $ (add_comm _ _).trans $ congr_arg2 _ n.choose_one_right.symm rfl

lemma d_nonpos_of_big {n : ℕ} (h0 : (z 0).nat_abs ≤ n.choose 2) : d z n ≤ 0 :=
  (binom_bound h n).trans $ int.sub_nonpos_of_le $ (le_abs_self _).trans $
    (z 0).coe_nat_abs.symm.trans_le $ int.coe_nat_le.mpr h0

lemma d_nonpos_mono {n : ℕ} (h0 : d z n ≤ 0) {k : ℕ} (h1 : n ≤ k) : d z k ≤ 0 :=
  nat.le_induction h0 (λ x _ h2, (main_lemma h x).trans $
    int.sub_nonpos_of_le $ h2.trans x.cast_nonneg) k h1

lemma d_one_pos (h0 : 0 < z 0) : 0 < d z 1 :=
  h0.trans_eq (d_one z).symm





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
    λ h1, (greatest_d_pos_is_d_pos h h0).not_le $ d_nonpos_of_big h $
      (congr_arg2 nat.choose h1.symm rfl).le.trans' $
      le_add_right (z 0).nat_abs.choose_one_right.ge

lemma eq_greatest_d_pos_iff {N : ℕ} : N = greatest_d_pos h ↔ 0 < d z N ∧ d z (N + 1) ≤ 0 :=
⟨λ h1, h1.symm ▸ ⟨greatest_d_pos_is_d_pos h h0, greatest_d_pos_succ_not_d_pos h h0⟩,
λ h1, le_antisymm
  (le_of_not_lt $ λ h2, h1.1.not_le $ d_nonpos_mono h (greatest_d_pos_succ_not_d_pos h h0) h2)
  (le_of_not_lt $ λ h2, (greatest_d_pos_is_d_pos h h0).not_le $ d_nonpos_mono h h1.2 h2)⟩





/- ### Final solution -/

/-- Final solution, part 1: `N` is positive. -/
theorem final_solution_part1 : 0 < greatest_d_pos h :=
  nat.pos_of_ne_zero $ λ h1, nat.find_greatest_eq_zero_iff.mp
    h1 nat.one_pos (nat.succ_pos _) (d_one_pos h h0)

/-- Final solution, part 2: `N` is indeed the index we are looking for. -/
theorem final_solution_part2 {N : ℕ} :
  N = greatest_d_pos h ↔
    (↑N * z N < (range (N + 1)).sum z ∧ (range (N + 1)).sum z ≤ N * z (N + 1)) :=
  (eq_greatest_d_pos_iff h h0).trans $ and_congr sub_pos $ (d_succ z N).symm ▸ sub_nonpos

/-- Final solution, extra: `C(N, 2) < z_0`, implemented as `C(N, 2) < (z 0).nat_abs`. -/
theorem final_solution_extra : (greatest_d_pos h).choose 2 < (z 0).nat_abs :=
  lt_of_not_le $ λ h1, (d_nonpos_of_big h h1).not_lt (greatest_d_pos_is_d_pos h h0)

end IMO2014A1
end IMOSL
