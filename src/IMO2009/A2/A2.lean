import algebra.order.field.basic tactic.ring tactic.field_simp

/-! # IMO 2009 A2 -/

namespace IMOSL
namespace IMO2009A2

section ring

variables {R : Type*} [linear_ordered_comm_ring R]

lemma two_var_AM_GM (a b : R) : 4 * (a * b) ≤ (a + b) ^ 2 :=
  by rw [bit0, add_mul, add_sq', ← mul_assoc];
    exact add_le_add_right (two_mul_le_add_sq a b) _

lemma two_var_AM_GM' (a b c : R) : 4 * ((c + a) * (a + b)) ≤ (2 * a + b + c) ^ 2 :=
  (two_var_AM_GM _ _).trans_eq $ congr_arg2 _ (by ring) rfl

lemma ring_identity1 (a b c : R) :
  (a + b) * (b + c) * (c + a) + a * b * c = (a + b + c) * (a * b + b * c + c * a) :=
  by ring

lemma ring_ineq1 {a b c : R} (h : 0 ≤ a) (h0 : 0 ≤ b) (h1 : 0 ≤ c) :
  8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a) :=
le_of_pow_le_pow 2
  (mul_nonneg (mul_nonneg (add_nonneg h h0) (add_nonneg h0 h1)) (add_nonneg h1 h))
  (nat.succ_pos 1) $
let X : ∀ x y : R, 0 ≤ x → 0 ≤ y → 0 ≤ 4 * (x * y) :=
  λ x y hx hy, mul_nonneg zero_le_four (mul_nonneg hx hy) in
by calc
(8 * (a * b * c)) ^ 2 = (4 * (a * b)) * (4 * (b * c)) * (4 * (c * a)) : by ring
... ≤ (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 :
  mul_le_mul
    (mul_le_mul (two_var_AM_GM a b) (two_var_AM_GM b c) (X b c h0 h1) (sq_nonneg _))
    (two_var_AM_GM c a) (X c a h1 h) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
... = ((a + b) * (b + c) * (c + a)) ^ 2 : by rw [mul_pow, mul_pow]

lemma ring_ineq2 {a b c : R} (h : 0 ≤ a) (h0 : 0 ≤ b) (h1 : 0 ≤ c) :
  8 * ((a + b + c) * (a * b + b * c + c * a)) ≤ 9 * ((a + b) * (b + c) * (c + a)) :=
    by rw [← ring_identity1, mul_add, bit1, add_one_mul];
      exact add_le_add_left (ring_ineq1 h h0 h1) _

lemma ring_identity2 (a b c : R) :
  2 * ((a * b + b * c + c * a) ^ 2 - 3 * (a * b * c * (a + b + c)))
    = (a * b - b * c) ^ 2 + (b * c - c * a) ^ 2 + (c * a - a * b) ^ 2 :=
  by ring

lemma ring_ineq3 (a b c : R) :
  3 * (a * b * c * (a + b + c)) ≤ (a * b + b * c + c * a) ^ 2 :=
  le_of_sub_nonneg $ nonneg_of_mul_nonneg_right
    ((add_nonneg (add_nonneg (sq_nonneg $ a * b - b * c) (sq_nonneg $ b * c - c * a))
      (sq_nonneg $ c * a - a * b)).trans_eq (ring_identity2 a b c).symm) two_pos

lemma ring_identity3 (a b c : R) : b + c + (c + a) + (a + b) = 2 * (a + b + c) :=
  by ring

end ring





lemma field_identity {F : Type*} [field F] {a b c : F} (h : a ≠ 0) (h0 : b ≠ 0) (h1 : c ≠ 0) :
  a * b * c * (a⁻¹ + b⁻¹ + c⁻¹) = a * b + b * c + c * a :=
begin
  rw [← add_rotate, mul_add, mul_add],
  refine congr_arg2 _ (congr_arg2 _ _ _) _,
  exact mul_inv_cancel_right₀ h1 _,
  rw [mul_assoc a b, mul_comm, inv_mul_cancel_left₀ h],
  rw [mul_right_comm a b, mul_inv_cancel_right₀ h0, mul_comm]
end

variables {F : Type*} [linear_ordered_field F]
  {a b c : F} (h : 0 < a) (h0 : 0 < b) (h1 : 0 < c)
include h h0 h1

lemma sym2_pos : 0 < a * b + b * c + c * a :=
  add_pos (add_pos (mul_pos h h0) (mul_pos h0 h1)) (mul_pos h1 h)

lemma intermediate_ineq :
  ((2 * a + b + c) ^ 2)⁻¹ + ((2 * b + c + a) ^ 2)⁻¹ + ((2 * c + a + b) ^ 2)⁻¹
    ≤ 9 / (16 * (a * b + b * c + c * a)) :=
begin
  have X : 0 < (4 : F) := four_pos,
  have X0 : 0 < a + b := add_pos h h0,
  have X1 : 0 < b + c := add_pos h0 h1,
  have X2 : 0 < c + a := add_pos h1 h,

  calc _ ≤ (4 * ((c + a) * (a + b)))⁻¹
    + (4 * ((a + b) * (b + c)))⁻¹ + (4 * ((b + c) * (c + a)))⁻¹ :
    let X3 : ∀ {x y z : F}, 0 < x → 0 < y → 0 < z →
      ((2 * x + y + z) ^ 2)⁻¹ ≤ (4 * ((z + x) * (x + y)))⁻¹ :=
      λ x y z hx hy hz, inv_le_inv_of_le
        (mul_pos X $ mul_pos (add_pos hz hx) (add_pos hx hy)) (two_var_AM_GM' x y z) in
      add_le_add_three (X3 h h0 h1) (X3 h0 h1 h) (X3 h1 h h0)
  ... = 4⁻¹ * (((c + a) * (a + b))⁻¹ + ((a + b) * (b + c))⁻¹ + ((b + c) * (c + a))⁻¹) :
    by rw [mul_inv, mul_inv (4 : F), mul_inv (4 : F), ← mul_add, ← mul_add]
  ... = 4⁻¹ * (((b + c) + (c + a) + (a + b)) / ((a + b) * (b + c) * (c + a))) :
    congr_arg2 has_mul.mul rfl $ begin
      rw [add_div, add_div],
      refine congr_arg2 _ (congr_arg2 _ _ _) _,
      rw [← mul_rotate, div_mul_left X1.ne.symm, one_div],
      rw [div_mul_left X2.ne.symm, one_div],
      rw [mul_rotate, div_mul_left X0.ne.symm, one_div]
    end
  ... ≤ 9 / (16 * (a * b + b * c + c * a)) : _,

  change (16 : F) with ((4 + 4) + (4 + 4) : F),
  rw [← two_mul, ← two_mul, ← mul_assoc, two_mul, ← bit0, inv_mul_le_iff X,
      mul_div, mul_assoc (4 : F), mul_div_mul_left _ _ X.ne.symm,
      div_le_div_iff (mul_pos (mul_pos X0 X1) X2) (mul_pos X $ sym2_pos h h0 h1)],
  refine (ring_ineq2 h.le h0.le h1.le).trans_eq' _,
  rw [ring_identity3, mul_mul_mul_comm, two_mul, ← bit0],
end





/-- Final solution -/
theorem final_solution (h2 : a⁻¹ + b⁻¹ + c⁻¹ = a + b + c) :
  ((2 * a + b + c) ^ 2)⁻¹ + ((2 * b + c + a) ^ 2)⁻¹ + ((2 * c + a + b) ^ 2)⁻¹ ≤ 3 / 16 :=
begin
  refine (intermediate_ineq h h0 h1).trans _,
  have h3 := ring_ineq3 a b c,
  have h4 : 0 < a * b + b * c + c * a := sym2_pos h h0 h1,
  rw [sq, ← h2, field_identity h.ne.symm h0.ne.symm h1.ne.symm, mul_le_mul_right h4] at h3,
  rw [← div_div, div_le_iff h4, div_mul_eq_mul_div],
  refine div_le_div_of_le_of_nonneg _ (zero_le_bit0.mpr $ zero_le_bit0.mpr zero_le_four),
  refine (mul_le_mul_of_nonneg_left h3 zero_le_three).trans_eq' _,
  norm_num
end

end IMO2009A2
end IMOSL
