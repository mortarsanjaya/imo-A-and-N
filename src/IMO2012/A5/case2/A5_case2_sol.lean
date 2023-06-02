import
  IMO2012.A5.case2.A5_case2_1
  IMO2012.A5.case2.A5_case2_2
  IMO2012.A5.case2.A5_case2_3
  IMO2012.A5.case2.A5_case2_4

/-! # IMO 2012 A5, Full Solution for Case 2: `f(-1) = 0` -/

namespace IMOSL
namespace IMO2012A5

variables {R S : Type*}

section noncomm_ring

variables [ring R] [ring S] [is_domain S] {f : R → S} (h : good f) (h0 : f (-1) = 0)
include h h0

lemma case2_map_sq_sub_one (h1 : f 0 = -1) (x : R) : f (x * x - 1) = f x * f x - 1 :=
  by rw [← case2_good_alt h h0, sub_self, h1, sub_neg_eq_add, add_sub_cancel]

lemma case2_map_two_values (h1 : f 0 = -1) : (f 2 = 3 ∨ (f 2 = 1 ∨ f 2 = -1)) ∨ f 2 = 0 :=
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

lemma case2_4_main_cases (h1 : f 2 = -1) (x : R) :
  f x + f (x - 1) = -1 ∨ f (x + 1) = f (x - 1) :=
  by have h2 := case2_special_identity h h0 x;
    rwa [case2_map_add_two_eq h h0, h1, mul_neg_one, neg_sub, sub_add_comm, mul_neg_one,
      neg_add_cancel_comm_assoc, mul_add, (map_comm_of_comm h (comm_self_sub_one x).symm).eq,
      ← sub_sub, sub_right_comm, ← mul_sub, ← neg_sub (f (x + 1)), mul_neg, ← neg_mul,
      ← sub_mul, sub_neg_eq_add, ← neg_one_mul, mul_eq_mul_right_iff, sub_eq_zero] at h2

lemma case2_4_periodic (h2 : f 2 = -1) (x : R) : f (2 + x) = f x :=
begin
  have h3 := case2_4_main_cases h h0 h2 (x + 1),
  rw [add_sub_cancel, add_assoc, add_comm x (1 + 1)] at h3,
  revert h3; refine (or_iff_right_of_imp $ λ h3, _).mp,
  have h4 := (case2_4_main_cases h h0 h2 (-(x + 1))).symm,
  rw [← neg_add', case2_map_is_even h h0, case2_map_is_even h h0, neg_add', sub_add_cancel,
      case2_map_is_even h h0, add_assoc, add_comm x (1 + 1), eq_comm] at h4,
  revert h4; refine (or_iff_left_of_imp $ λ h4, _).mp,
  rwa [← h3, add_right_inj] at h4
end

end noncomm_ring



section solution

/- Needs to be filled in -/

end solution

end IMO2012A5
end IMOSL
