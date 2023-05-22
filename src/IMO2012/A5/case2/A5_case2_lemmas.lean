import IMO2012.A5.A5_basic algebra.group_power.ring

/-! # IMO 2012 A5, Case 2: `f(-1) = 0` -/

namespace IMOSL
namespace IMO2012A5

section non_domain

variables {R S : Type*} [ring R] [ring S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)
include h h0

lemma case2_map_is_even (x : R) : f (-x) = f x :=
  sub_eq_zero.mp $ (map_neg_sub_map2 h x).trans $ mul_eq_zero_of_right (f (x + 1)) h0

lemma case2_good_alt (x y : R) : f (x * y - 1) - f (x - y) = f x * f y :=
  by rw [← case2_map_is_even h h0 y, ← h, mul_neg, ← sub_eq_add_neg,
    ← case2_map_is_even h h0, neg_sub, neg_add_eq_sub]

lemma case2_map_add_two_eq (x : R) : f (x + 2) = (f (x + 1) - f x) * f 2 + f (x - 1) :=
  by rw [sub_mul, ← add_sub_right_comm, eq_sub_iff_add_eq', ← map_mul_two_add_one h,
    ← case2_map_is_even h h0, neg_add', ← neg_mul, ← sub_add_cancel (-x * 2 - 1) 1,
    sub_sub, ← bit0, ← sub_one_mul, map_mul_two_add_one h, bit0, sub_add_add_cancel,
    ← neg_add', case2_map_is_even h h0, neg_add_eq_sub, ← neg_sub x, case2_map_is_even h h0]

lemma case2_special_identity (x : R) :
  f x * f (x + 1) - f (x - 1) * f (x + 2) = f x * f 2 + f (x + 2) :=
  by rw [← map_mul_two_add_one h, ← case2_good_alt h h0, sub_add_cancel', h0,
    sub_zero, ← h, bit0, ← add_assoc, sub_add_add_cancel, ← add_assoc, ← mul_two,
    ← sub_add, bit0, add_left_eq_self, sub_eq_zero, mul_add_one (x - 1), add_assoc,
    sub_add_cancel, sub_one_mul, sub_add_comm, sub_add_cancel', neg_add_eq_sub]

variables (h1 : f 0 = -1)
include h1

lemma case2_map_sq_sub_one (x : R) : f (x * x - 1) = f x * f x - 1 :=
  by rw [← case2_good_alt h h0, sub_self, h1, sub_neg_eq_add, add_sub_cancel]

end non_domain



lemma case2_map_two_values {R S : Type*} [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 0 = -1) :
  (f 2 = 3 ∨ (f 2 = 1 ∨ f 2 = -1)) ∨ f 2 = 0 :=
begin
  replace h1 := case2_map_sq_sub_one h h0 h1 2,
  rw [two_mul, bit0, ← add_assoc, add_sub_cancel, ← bit0] at h1,
  have h2 := case2_good_alt h h0 3 2,
  rwa [bit1, add_sub_cancel', good_map_one h, sub_zero, add_one_mul, bit0, ← add_assoc,
    add_sub_cancel, ← bit0, two_mul, add_right_comm, case2_map_add_two_eq h h0, add_assoc,
    add_sub_cancel, ← add_one_mul, mul_eq_mul_right_iff, ← bit0, ← add_sub_right_comm,
    sub_eq_iff_eq_add, case2_map_add_two_eq h h0, bit0, add_sub_cancel, good_map_one h,
    add_zero, ← bit0, sub_mul, sub_add, ← h1, ← mul_two, sub_eq_iff_eq_add,
    ← mul_add_one, mul_eq_mul_left_iff, h1, sub_eq_zero, mul_self_eq_one_iff] at h2
end

end IMO2012A5
end IMOSL
