import IMO2012.A5.A5_basic

/-! # IMO 2012 A5, General Lemmas for Case 2: `f(-1) = 0`

Note: the lemmas are not used for Subcase 2.4 except for obtaining `2 = 0` in `R`. -/

namespace IMOSL
namespace IMO2012A5

variables {R S : Type*} [ring R] [ring S] {f : R → S} (h : good f) (h0 : f (-1) = 0)
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

end IMO2012A5
end IMOSL
