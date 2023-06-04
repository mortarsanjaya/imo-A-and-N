import data.int.parity tactic.ring

/-! # IMO 2014 N2 -/

namespace IMOSL
namespace IMO2014N2

def good (x y : ℤ) := 7 * (x ^ 2 + y ^ 2) - 13 * (x * y) = (|x - y| + 1) ^ 3





/-! ## Identities -/
lemma identity1 (m n : ℤ) : (2 * m + n) ^ 2 = 4 * ((m + n) * m) + n ^ 2 :=
  by ring

lemma identity2 (m n : ℤ) :
  7 * (m ^ 2 + n ^ 2) - 13 * (m * n) = (n + (m - n)) * n + 7 * (m - n) ^ 2 :=
  by ring

lemma identity3 (n : ℤ) :
  4 * ((n + 1) ^ 3 - 7 * n ^ 2) + n ^ 2 = (n - 2) ^ 2 * (4 * n + 1) :=
  by ring



/-! ## Start of the solution -/
def A (m : ℤ) := m ^ 3 + 2 * m ^ 2 - m - 1
def B (m : ℤ) := m ^ 3 + m ^ 2 - 2 * m - 1

lemma A_sub_B (m : ℤ) : A m - B m = (m + 1) * m :=
  by rw [A, B]; ring

lemma good_A_B (m : ℤ) : good (A m) (B m) :=
  suffices 0 ≤ (m + 1) * m,
    by rw [good, A_sub_B, abs_eq_self.mpr this, A, B]; ring,
  (le_or_lt 0 m).elim (λ h, mul_nonneg (add_nonneg h zero_le_one) h)
    (λ h, mul_nonneg_of_nonpos_of_nonpos (int.add_one_le_iff.mpr h) (le_of_lt h))

lemma good_swap {x y : ℤ} (h : good x y) : good y x :=
  (congr_arg2 (λ u v : ℤ, 7 * u - 13 * v) (add_comm _ _) (mul_comm y x)).trans $
    h.trans $ congr_arg (λ u : ℤ, (u + 1) ^ 3) (abs_sub_comm x y)

lemma good_le_imp {x y : ℤ} (h : good x y) (h0 : y ≤ x) : ∃ m : ℤ, x = A m ∧ y = B m :=
begin
  ---- Rearrange to get `(2y + n)^2 = (n - 2)^2 (4n + 1)`, where `n = x - y`
  rw ← sub_nonneg at h0,
  rw [good, abs_eq_self.mpr h0, identity2, ← eq_sub_iff_add_eq] at h,
  replace h := congr_arg (has_mul.mul 4) h,
  rw [← add_left_inj ((x - y) ^ 2), ← identity1, identity3] at h,

  ---- `(n - 2)^2 = 0` or `k^2 = 4n + 1` for some `k : ℤ`
  obtain ⟨k, h1⟩ : (x - y) - 2 ∣ 2 * y + (x - y) :=
    (int.pow_dvd_pow_iff $ nat.succ_pos 1).mp ⟨4 * (x - y) + 1, h⟩,
  rw [h1, mul_pow, mul_eq_mul_left_iff, or_comm] at h,
  have X : (0 : ℤ) < 2 := int.bit0_pos int.one_pos, -- Several steps use this Prop
  cases h with h h,

  ---- Case 1: `n - 2 = 0`
  { replace h := sub_eq_zero.mp (pow_eq_zero h),
    rw [h, sub_self, zero_mul, ← mul_add_one, mul_eq_zero,
        add_eq_zero_iff_eq_neg, or_iff_right (ne_of_gt X)] at h1,
    rw [h1, sub_neg_eq_add, bit0, add_left_inj] at h,
    refine ⟨1, _, _⟩,
    rw [A, h]; norm_num,
    rw [B, h1]; norm_num },

  ---- Case 2: `k^2 = 4n + 1` for some `k : ℤ`
  { obtain ⟨m, rfl⟩ : ∃ m : ℤ, 2 * m + 1 = k :=
      ⟨k / 2, int.two_mul_div_two_add_one_of_odd $ by rw [int.odd_iff_not_even,
        ← int.even_pow' two_ne_zero, h, ← int.odd_iff_not_even];
          exact ⟨(2 : ℤ) * (x - y), congr_arg (+ (1 : ℤ)) (mul_assoc 2 2 (x - y))⟩⟩,
    rw [identity1, one_pow, add_left_inj, mul_eq_mul_left_iff,
        or_iff_left (ne_of_gt $ int.bit0_pos X)] at h,
    rw [← eq_sub_iff_add_eq, mul_add_one, add_sub_assoc, sub_sub_cancel_left,
        ← sub_eq_add_neg, mul_left_comm, ← mul_sub_one, mul_eq_mul_left_iff,
        or_iff_left (ne_of_gt X), ← h] at h1,
    refine ⟨m, _, _⟩,
    rw [← sub_add_cancel x y, ← h, h1, A]; ring,
    rw [h1, B]; ring }
end

/-- Final solution -/
theorem final_solution (x y : ℤ) :
  good x y ↔ ((∃ m : ℤ, x = A m ∧ y = B m) ∨ (∃ m : ℤ, y = A m ∧ x = B m)) :=
  ⟨λ h, (le_total y x).imp (good_le_imp h) (good_le_imp $ good_swap h),
  λ h, h.elim
    (λ h0, exists.elim h0 $ λ m h1,
      cast (congr_arg2 good h1.1.symm h1.2.symm) $ good_A_B m)
    (λ h0, exists.elim h0 $ λ m h1,
      cast (congr_arg2 good h1.2.symm h1.1.symm) $ good_swap $ good_A_B m)⟩

end IMO2014N2
end IMOSL
