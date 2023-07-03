import algebra.order.field.basic extra.fin4

/-! # IMO 2020 A3, General Version (Lower Bound and Restricted Equality) -/

namespace IMOSL
namespace IMO2020A3

open extra extra.fin4

def good {R : Type*} [ring R] (x : fin4 → R) :=
  (x i1 + x i3) * (x i2 + x i4) = x i1 * x i3 + x i2 * x i4

def target_val {F : Type*} [field F] (x : fin4 → F) :=
  (x i1 / x i2 + x i2 / x i3) + (x i3 / x i4 + x i4 / x i1)



section ordered_comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]

lemma AM_GM2 (a b : R) : 4 * (a * b) ≤ (a + b) ^ 2 :=
  by rw [add_sq', bit0, add_mul, ← mul_assoc, add_le_add_iff_right];
    exact two_mul_le_add_sq a b

lemma good_ring_bound {x : fin4 → R} (h : ∀ i, 0 ≤ x i) (h0 : good x) :
  4 ^ 2 * ((x i1 * x i3) * (x i2 * x i4)) ≤ (x i1 * x i3 + x i2 * x i4) ^ 2 :=
  by rw [sq, mul_mul_mul_comm, h0.symm, mul_pow]; exact mul_le_mul (AM_GM2 _ _)
    (AM_GM2 _ _) (mul_nonneg zero_le_four $ mul_nonneg (h i2) (h i4)) (sq_nonneg _)

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



section lower_bound
  
variables {x : fin4 → F} (h : ∀ i, 0 < x i)
include h

lemma target_val_general_bound :
  4 * ((x i1 * x i3) / (x i2 * x i4) + (x i2 * x i4) / (x i1 * x i3) + 2) ≤ target_val x ^ 2 :=
begin
  ---- Use AM-GM on `x_0/x_1 + x_2/x_3` and `x_1/x_2 + x_3/x_0`
  have h1 := AM_GM_fractions (x i1) (x i2) (x i3) (x i4),
  have h2 := AM_GM_fractions (x i2) (x i3) (x i4) (x i1),
  rw mul_comm (x i3) at h2,

  ---- Reduce to `4 ≤ (x_0/x_1 + x_2/x_3)(x_1/x_2 + x_3/x_0)`
  rw [mul_add, mul_add, target_val, add_add_add_comm, add_sq', mul_assoc, mul_comm (4 : F) 2],
  refine add_le_add (add_le_add h1 h2) (mul_le_mul_of_nonneg_left _ zero_le_two),
  
  ---- Final step
  have h0 := mul_pos (h i2) (h i4),
  have h3 := mul_pos (h i1) (h i3),
  replace h1 := mul_le_mul h1 h2
    (mul_nonneg zero_le_four $ le_of_lt $ div_pos h0 h3) (sq_nonneg _),
  rw [mul_mul_mul_comm, div_mul_div_cancel _ (ne_of_gt h0),
      div_self (ne_of_gt h3), mul_one, ← sq, ← mul_pow] at h1,
  exact (abs_le_of_sq_le_sq' h1 $ le_of_lt $ mul_pos
    (div_add_div_pos (h i1) (h i2) (h i3) (h i4))
    (div_add_div_pos (h i2) (h i3) (h i4) (h i1))).2
end

lemma target_val_pos : 0 < target_val x :=
  add_pos (div_add_div_pos (h i1) (h i2) (h i2) (h i3))
    (div_add_div_pos (h i3) (h i4) (h i4) (h i1))

lemma good_field_bound (h0 : good x) :
  4 ^ 2 ≤ (x i1 * x i3) / (x i2 * x i4) + (x i2 * x i4) / (x i1 * x i3) + 2 :=
  let h1 := mul_pos (h i1) (h i3), h2 := mul_pos (h i2) (h i4),
    h3 := ne_of_gt h1, h4 := ne_of_gt h2 in
  by rw [div_add_div _ _ h4 h3, ← sq, ← sq, mul_comm (x i2 * x i4),
    div_add' _ _ _ (mul_ne_zero h3 h4), ← mul_assoc,
    ← add_sq', le_div_iff (mul_pos h1 h2)];
  exact good_ring_bound (λ i, le_of_lt $ h i) h0

lemma target_val_good_bound (h0 : good x) : 8 ≤ target_val x :=
  and.right $ abs_le_of_sq_le_sq'
    (le_trans (le_of_eq_of_le eight_sq_eq_four_mul_four_sq
        (mul_le_mul_of_nonneg_left (good_field_bound h h0) zero_le_four))
      (target_val_general_bound h))
    (le_of_lt $ target_val_pos h)

end lower_bound



section upper_bound

def good_infarg (c : F) : fin4 → F
| i1 := 2 + c
| i2 := 1
| i3 := 2 + c
| i4 := 1

lemma infarg_is_pos {c : F} (h0 : 0 < c) : ∀ i : fin4, 0 < good_infarg c i
| i1 := add_pos two_pos h0
| i2 := one_pos
| i3 := add_pos two_pos h0
| i4 := one_pos

variables {c : F} (h : c * c = 3)
include h

lemma two_add_sqrt3_mul_two_sub_sqrt3_eq_one : (2 + c) * (2 - c) = 1 :=
  (mul_self_sub_mul_self 2 c).symm.trans $ (congr_arg2 has_sub.sub (mul_two 2) h).trans $
    (add_sub_add_left_eq_sub 2 1 2).trans $ add_sub_cancel 1 1

lemma infarg_is_good : good (good_infarg c) :=
  calc (2 + c + (2 + c)) * (1 + 1) = (2 + c) * 2 * 2 :
    congr_arg2 has_mul.mul (mul_two (2 + c)).symm rfl
  ... = (2 + c) * (2 + c) + (2 + c) * (2 - c) :
    by rw [← mul_add, add_add_sub_cancel, ← two_mul, mul_assoc]
  ... = (2 + c) * (2 + c) + 1 * 1 : congr_arg (has_add.add _) $
    (two_add_sqrt3_mul_two_sub_sqrt3_eq_one h).trans (mul_one 1).symm

lemma target_val_infarg : target_val (good_infarg c) = 8 :=
  suffices (2 + c) / 1 + 1 / (2 + c) = 4, from congr_arg2 has_add.add this this,
  (congr_arg2 has_add.add (div_one _) (eq_one_div_of_mul_eq_one_right $
    two_add_sqrt3_mul_two_sub_sqrt3_eq_one h).symm).trans $ add_add_sub_cancel 2 2 c

lemma target_val_minimum (h0 : 0 < c) :
  is_least ((λ x : fin4 → F, target_val x) '' {x | (∀ i : fin4, 0 < x i) ∧ good x}) 8 :=
  ⟨⟨good_infarg c, ⟨infarg_is_pos h0, infarg_is_good h⟩, target_val_infarg h⟩,
  λ c h, exists.elim h $ λ x h0, le_of_le_of_eq (target_val_good_bound h0.1.1 h0.1.2) h0.2⟩

end upper_bound

end ordered_field

end IMO2020A3
end IMOSL
