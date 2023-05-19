import algebra.order.field.basic

/-! # IMO 2020 A3, General Version (Lower Bound only) -/

namespace IMOSL
namespace IMO2020A3

def good {R : Type*} [ring R] (x : fin 4 → R) :=
  (x 0 + x 2) * (x 1 + x 3) = x 0 * x 2 + x 1 * x 3

def target_val {F : Type*} [field F] (x : fin 4 → F) :=
  x 0 / x 1 + x 1 / x 2 + x 2 / x 3 + x 3 / x 0



section ordered_comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]

lemma AM_GM2 (a b : R) : 4 * (a * b) ≤ (a + b) ^ 2 :=
  by rw [add_sq', bit0, add_mul, ← mul_assoc, add_le_add_iff_right];
    exact two_mul_le_add_sq a b

lemma good_ring_bound {x : fin 4 → R} (h : ∀ i, 0 ≤ x i) (h0 : good x) :
  4 ^ 2 * ((x 0 * x 2) * (x 1 * x 3)) ≤ (x 0 * x 2 + x 1 * x 3) ^ 2 :=
  by rw [sq, mul_mul_mul_comm, h0.symm, mul_pow]; exact mul_le_mul (AM_GM2 _ _)
    (AM_GM2 _ _) (mul_nonneg zero_le_four $ mul_nonneg (h 1) (h 3)) (sq_nonneg _)

end ordered_comm_ring



section ordered_field

variables {F : Type*} [linear_ordered_field F]

lemma AM_GM_fractions (a b c d : F) : 4 * ((a * c) / (b * d)) ≤ (a / b + c / d) ^ 2 :=
  le_of_le_of_eq' (AM_GM2 (a / b) (c / d)) $
    congr_arg (has_mul.mul 4) (div_mul_div_comm a b c d).symm

lemma div_add_div_pos {a b c d : F} (h : 0 < a) (h0 : 0 < b) (h1 : 0 < c) (h2 : 0 < d) :
  0 < a / b + c / d :=
  add_pos (div_pos h h0) (div_pos h1 h2)

lemma eight_sq_eq_four_mul_four_sq : (8 : F) ^ 2 = 4 * 4 ^ 2 :=
  by rw [bit0, ← two_mul, mul_pow, sq, two_mul, ← bit0]
  
variables {x : fin 4 → F} (h : ∀ i, 0 < x i)
include h

lemma target_val_general_bound :
  4 * ((x 0 * x 2) / (x 1 * x 3) + (x 1 * x 3) / (x 0 * x 2) + 2) ≤ target_val x ^ 2 :=
begin
  ---- Use AM-GM on `x_0/x_1 + x_2/x_3` and `x_1/x_2 + x_3/x_0`
  have h1 := AM_GM_fractions (x 0) (x 1) (x 2) (x 3),
  have h2 := AM_GM_fractions (x 1) (x 2) (x 3) (x 0),
  rw mul_comm (x 2) at h2,

  ---- Reduce to `4 ≤ (x_0/x_1 + x_2/x_3)(x_1/x_2 + x_3/x_0)`
  rw [mul_add, mul_add, target_val, add_assoc _ (x 2 / x 3),
      add_add_add_comm, add_sq', mul_assoc, mul_comm (4 : F) 2],
  refine add_le_add (add_le_add h1 h2) (mul_le_mul_of_nonneg_left _ zero_le_two),
  
  ---- Final step
  have h0 := mul_pos (h 1) (h 3),
  have h3 := mul_pos (h 0) (h 2),
  replace h1 := mul_le_mul h1 h2
    (mul_nonneg zero_le_four $ le_of_lt $ div_pos h0 h3) (sq_nonneg _),
  rw [mul_mul_mul_comm, div_mul_div_cancel _ (ne_of_gt h0),
      div_self (ne_of_gt h3), mul_one, ← sq, ← mul_pow] at h1,
  exact (abs_le_of_sq_le_sq' h1 $ le_of_lt $ mul_pos
    (div_add_div_pos (h 0) (h 1) (h 2) (h 3)) (div_add_div_pos (h 1) (h 2) (h 3) (h 0))).2
end

lemma target_val_pos : 0 < target_val x :=
  add_pos (add_pos (div_add_div_pos (h 0) (h 1) (h 1) (h 2)) (div_pos (h 2) (h 3)))
    (div_pos (h 3) (h 0))

lemma good_field_bound (h0 : good x) :
  4 ^ 2 ≤ (x 0 * x 2) / (x 1 * x 3) + (x 1 * x 3) / (x 0 * x 2) + 2 :=
  let h1 := mul_pos (h 0) (h 2), h2 := mul_pos (h 1) (h 3),
    h3 := ne_of_gt h1, h4 := ne_of_gt h2 in
  by rw [div_add_div _ _ h4 h3, ← sq, ← sq, mul_comm (x 1 * x 3),
    div_add' _ _ _ (mul_ne_zero h3 h4), ← mul_assoc,
    ← add_sq', le_div_iff (mul_pos h1 h2)];
  exact good_ring_bound (λ i, le_of_lt $ h i) h0

lemma target_val_good_bound (h0 : good x) : 8 ≤ target_val x :=
  and.right $ abs_le_of_sq_le_sq'
    (le_trans (le_of_eq_of_le eight_sq_eq_four_mul_four_sq
        (mul_le_mul_of_nonneg_left (good_field_bound h h0) zero_le_four))
      (target_val_general_bound h))
    (le_of_lt $ target_val_pos h)

end ordered_field

end IMO2020A3
end IMOSL
