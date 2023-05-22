import IMO2012.A5.A5_basic algebra.ring.commute

/-! # IMO 2012 A5, Case 1: `f(-1) ≠ 0` -/

namespace IMOSL
namespace IMO2012A5

variables {R S : Type*} [ring R] [ring S]

/-- While this lemma does not depend on `f(-1) ≠ 0`, it is useless in the case `f(-1) = 0`. -/
lemma case1_map_add_main_equality {f : R → S} (h : good f) (x y : R) :
  -f (x + y + 1) * f (-1) = f (-x) * f (-y) - f x * f y :=
  by rw [← h, ← h, neg_mul_neg, sub_sub_sub_cancel_left,
    ← neg_add, ← neg_sub, map_neg_sub_map2 h, neg_mul]



variables [is_domain S] {f : R → S} (h : good f) (h0 : f (-1) ≠ 0)
include h h0

lemma case1_map_neg_add_one (x : R) : f (-x + 1) = -f (x + 1) :=
  by rw [← mul_left_inj' h0, ← map_neg_sub_map2 h,
    neg_neg, neg_mul, ← map_neg_sub_map2 h, neg_sub]

lemma case1_map_neg (x : R) : f (-x) = -f (x + 2) :=
  by rw [bit0, ← add_assoc, ← case1_map_neg_add_one h h0,
    neg_add_rev, neg_add_cancel_comm]

lemma case1_map_add_two (x : R) : f (x + 2) = f (x + 1) * -f (-1) - f x :=
  by rw [mul_neg, ← map_neg_sub_map2 h, neg_sub,
    sub_sub_cancel_left, case1_map_neg h h0, neg_neg]

lemma case1_map_zero : f 0 = -1 :=
  not_not.mp $ λ h1, h0 $
    (congr_fun (eq_zero_of_map_zero_ne_neg_one h h1) _).trans rfl

lemma case1_map_two : f 2 = 1 :=
  by rw [bit0, ← neg_inj, ← case1_map_neg_add_one h h0, neg_add_self];
    exact case1_map_zero h h0

lemma case1_map_two_mul_add_one (x : R) : f (x * 2 + 1) = f x - f (-x) :=
  by rw [map_mul_two_add_one h, case1_map_two h h0,
    mul_one, case1_map_neg h h0, sub_neg_eq_add]

lemma case1_map_ne_zero_imp {x : R} (h1 : f x ≠ 0) : f (x - 1) - f (x + 1) = f (-1) :=
  by have h2 := case1_map_add_main_equality h (x - 1) (x - 1);
  rwa [(map_comm_of_comm h (commute.refl $ x - 1).neg_left).mul_self_sub_mul_self_eq',
    ← mul_two, case1_map_two_mul_add_one h h0, neg_sub, map_neg_sub_map2 h,
    sub_add_cancel, mul_right_inj' (mul_ne_zero h1 h0), neg_sub', sub_neg_eq_add,
    case1_map_neg_add_one h h0, add_comm, ← sub_eq_add_neg, eq_comm] at h2

lemma case1_map_eq_zero_imp {x : R} (h1 : f x = 0) : f (x + 1) = 1 ∧ f (x - 1) = -1 :=
begin
  /- Current code takes about 0.2s... can we optimize it? -/
  have h2 := map_neg_sub_map1 h x,
  rw [h1, zero_mul, sub_eq_zero, sub_eq_add_neg, add_comm] at h2,
  rw [← h2, case1_map_neg_add_one h h0, neg_inj, and_self],
  have h3 := case1_map_two_mul_add_one h h0 (x - 1),
  rw [sub_one_mul, bit0, ← sub_sub, sub_add_cancel,
      neg_sub', sub_neg_eq_add, h2, sub_self] at h3,
  replace h2 := case1_map_add_main_equality h (x - 1) x,
  rw [h1, mul_zero, sub_zero, ← add_sub_right_comm, neg_mul,
      ← map_neg_sub_map2 h, ← mul_two, bit0, h3, sub_zero, neg_sub',
      sub_neg_eq_add, neg_sub', sub_neg_eq_add, ← bit0] at h2,
  replace h3 := case1_map_two_mul_add_one h h0 (-x),
  rw [neg_neg, map_neg_sub_map2 h] at h3,
  rw [← neg_mul, h3, case1_map_neg_add_one h h0, neg_mul, neg_inj,
      mul_eq_mul_left_iff, ← mul_eq_mul_right_iff] at h2,
  replace h3 := case1_map_add_main_equality h x (-(x + 1)),
  rwa [h1, zero_mul, sub_zero, neg_neg, add_right_comm,
       add_neg_self, case1_map_zero h h0, neg_neg, one_mul,
       ← h2, eq_comm, mul_right_eq_self₀, or_iff_left h0] at h3
end

lemma case1_map_neg_one_values : f (-1) = -2 ∨ f (-1) = 1 :=
begin
  have h1 := case1_map_neg h h0 1,
  rw [← neg_eq_iff_eq_neg, add_comm] at h1,
  have h2 := h 2 2,
  rwa [mul_two, add_right_comm, case1_map_add_two h h0, add_assoc, ← bit0,
       sub_right_comm, ← mul_sub_one, case1_map_add_two h h0, case1_map_two h h0,
       sub_eq_iff_eq_add', ← h1, mul_one, mul_self_sub_one, mul_assoc,
       mul_right_eq_self₀, neg_add_eq_zero, mul_self_eq_one_iff, sub_eq_neg_self,
       neg_eq_zero, or_iff_left h0, sub_eq_iff_eq_add, neg_eq_iff_eq_neg] at h2
end

end IMO2012A5
end IMOSL
