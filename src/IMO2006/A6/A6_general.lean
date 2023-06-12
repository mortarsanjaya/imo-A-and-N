import algebra.order.ring.abs tactic.ring

/-! # IMO 2006 A6 (P3), General Version (Lower Bound and Restricted Equality) -/

namespace IMOSL
namespace IMO2006A6

def good {R : Type*} [linear_ordered_comm_ring R] (M : R) :=
  ∀ a b c : R, |a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)|
    ≤ M * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2



section special_identities

variables {R : Type*} [comm_ring R]

lemma special_identity1 (a b c : R) :
  a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2)
    = (b - a) * (c - b) * (a - c) * (a + b + c) :=
  by ring

lemma special_identity2 (a b c : R) :
  (b - a) ^ 2 + (c - b) ^ 2 + (a - c) ^ 2 + (a + b + c) ^ 2
    = 3 * (a ^ 2 + b ^ 2 + c ^ 2) :=
  by ring

end special_identities



variables {R : Type*} [linear_ordered_comm_ring R]

lemma AM_GM_1_to_3 (x y : R) : 2 ^ 8 * x ^ 3 * y ≤ ((3 * x + y) ^ 2) ^ 2 :=
  le_of_sub_nonneg $ by calc
  0 ≤ (x - y) ^ 2 * ((7 * x + y) ^ 2 + 2 ^ 5 * x ^ 2) : mul_nonneg (sq_nonneg _) $
    add_nonneg (sq_nonneg _) $ mul_nonneg (pow_nonneg zero_le_two 5) (sq_nonneg _)
  ... = _ : by ring

lemma AM_GM_sq_of_sum_eq_zero {x y z : R} (h : x + y + z = 0) :
  2 * ((3 ^ 2) ^ 2 * (x * y * z) ^ 2) ≤ (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 * 3 :=
  le_of_sub_nonneg $ by calc
  0 ≤ 2 * 3 * ((x - y) * (x + 2 * y) * (2 * x + y)) ^ 2 :
    mul_nonneg (mul_nonneg zero_le_two zero_le_three) (sq_nonneg _)
  ... = (x ^ 2 + y ^ 2 + (-(x + y)) ^ 2) ^ 3 * 3
    - 2 * ((3 ^ 2) ^ 2 * (x * y * -(x + y)) ^ 2) : by ring
  ... = _ : by rw ← eq_neg_of_add_eq_zero_right h

lemma good_of_ineq {M : R} (h : 0 ≤ M) (h0 : (3 ^ 2) ^ 2 ≤ 2 ^ 9 * M ^ 2) : good M :=
begin
  intros a b c,
  have X2 : 0 < (2 : R) := two_pos,
  rw [special_identity1, ← abs_sq (a ^ 2 + b ^ 2 + c ^ 2), ← abs_eq_self.mpr h,
      ← abs_mul, abs_le_iff_mul_self_le, ← sq, ← sq, mul_pow, mul_pow M,
      ← mul_le_mul_left (pow_pos X2 9), ← mul_assoc, ← mul_assoc],
  refine le_trans _ (mul_le_mul_of_nonneg_right h0 $ sq_nonneg _),
  have X3 : 0 < (3 : R) := three_pos,
  rw [← mul_pow, ← mul_pow, ← mul_le_mul_left (pow_pos (pow_pos X3 2) 2),
      ← special_identity2, ← mul_pow, ← mul_pow, mul_add],
  refine le_trans _ (AM_GM_1_to_3 _ _),
  rw [← mul_assoc, ← mul_assoc _ (3 : R)],
  refine mul_le_mul_of_nonneg_right _ (sq_nonneg _),
  rw [mul_left_comm, pow_succ', mul_assoc, mul_assoc (2 ^ 8 : R)],
  exact mul_le_mul_of_nonneg_left (AM_GM_sq_of_sum_eq_zero $ by ring) (pow_bit0_nonneg 2 4)
end

lemma ineq_of_good {sqrt2 : R} (h : 0 ≤ sqrt2) (h0 : sqrt2 ^ 2 = 2) {M : R} (h1 : good M) :
  3 ^ 2 * sqrt2 ≤ M * 2 ^ 5 :=
begin
  replace h1 := h1 sqrt2 (sqrt2 - 3) (sqrt2 + 3),
  rw [special_identity1, sub_sub_cancel_left, add_sub_sub_cancel, sub_add_cancel', add_assoc,
      sub_add_add_cancel, sub_sq', add_sq' sqrt2 3, h0, add_assoc, sub_add_add_cancel] at h1,
  replace h0 : (-3) * (3 + 3) * (-3) * (sqrt2 + (sqrt2 + sqrt2)) = 18 * 3 ^ 2 * sqrt2 := by ring,
  rw [h0, abs_mul, abs_mul, abs_sq, abs_eq_self.mpr h] at h1,
  replace h0 : (2 + (2 + 3 ^ 2 + (2 + 3 ^ 2)) : R) ^ 2 = 18 * 2 ^ 5 := by norm_num,
  rw [h0, mul_left_comm] at h1,
  replace h0 : 0 < (18 : R) := bit0_pos (bit1_pos zero_le_four),
  rwa [abs_eq_self.mpr (le_of_lt h0), mul_assoc, mul_le_mul_left h0] at h1
end

lemma good_iff' {sqrt2 : R} (h : 0 ≤ sqrt2) (h0 : sqrt2 ^ 2 = 2) (M : R) :
  good M ↔ 3 ^ 2 * sqrt2 ≤ M * 2 ^ 5 :=
  ⟨ineq_of_good h h0, λ h1, begin
    have h2 : 0 < (2 : R) ^ 5 := pow_pos two_pos 5,
    have h3 : 0 ≤ 3 ^ 2 * sqrt2 := mul_nonneg (sq_nonneg 3) h,
    have h4 : 0 ≤ M := nonneg_of_mul_nonneg_left (h3.trans h1) h2,
    refine good_of_ineq h4 _,
    rw [← abs_eq_self.mpr h3, ← abs_eq_self.mpr h4, ← abs_eq_self.mpr (le_of_lt h2),
        ← abs_mul, ← sq_le_sq, mul_pow, h0, mul_pow, ← pow_mul (2 : R) 5, mul_two 5,
        ← bit0, pow_succ' (2 : R), mul_left_comm, ← mul_assoc] at h1,
    exact (mul_le_mul_right two_pos).mp h1
  end⟩

lemma good_iff {sqrt2 : R} (h : 0 ≤ sqrt2) (h0 : sqrt2 ^ 2 = 2) (M : R) :
  good M ↔ 9 * sqrt2 ≤ M * 32 :=
  (good_iff' h h0 M).trans $ by norm_num

end IMO2006A6
end IMOSL
