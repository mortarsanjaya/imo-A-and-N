import IMO2012.A5.case1.A5_case1_lemmas

/-! # IMO 2012 A5, Case 1.1: `f(-1) = 2 ≠ 0` -/

namespace IMOSL
namespace IMO2012A5

variables {R S : Type*} [ring R] [ring S]

/-- The respective solution for the subcase. -/
theorem case1_1_answer : good (λ x : R, x - 1) :=
  λ x y, by rw [sub_sub_sub_cancel_right, ← sub_sub_sub_eq, ← mul_sub_one, ← sub_one_mul]



variables [is_domain S] {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) (h1 : f (-1) = -2)
include h h0 h1

private lemma case1_1_lem1 (x : R) : f (x - 1) - f (x + 1) = -2 :=
  (eq_or_ne (f x) 0).elim
  (λ h2, let h3 := case1_map_eq_zero_imp h h0 h2 in by rw [h3.1, h3.2, ← neg_add', bit0])
  (λ h2, (case1_map_ne_zero_imp h h0 h2).trans h1)

private lemma case1_1_lem2 (x : R) : f (-x) = -(f x + 2) :=
  by rw [case1_map_neg h h0, neg_add_rev, ← case1_1_lem1 h h0 h1 (x + 1),
    add_sub_cancel, ← sub_eq_add_neg, sub_sub_cancel_left, bit0, add_assoc]

private lemma case1_1_lem3 (x : R) : f (x + 1) = f x + 1 :=
  by have h2 := map_neg_sub_map2 h x; rwa [case1_1_lem2 h h0 h1, ← neg_add',
    add_right_comm, ← mul_two, ← add_one_mul, ← mul_neg, ← h1, mul_left_inj' h0, eq_comm] at h2

private lemma case1_1_lem4 (x y : R) : f (x + y) = f x + f y + 1 :=
  let h3 := case1_1_lem2 h h0 h1 in
  by have h2 := case1_map_add_main_equality h x y;
  rwa [h1, neg_mul_neg, h3, h3, neg_mul_neg, add_mul, mul_add, mul_add,
    two_mul, ← mul_two, add_assoc (f x * f y), add_sub_cancel', ← add_mul,
    ← add_mul, mul_left_inj' (neg_ne_zero.mp $ ne_of_eq_of_ne h1.symm h0),
    case1_1_lem3 h h0 h1, bit0, ← add_assoc, ← add_assoc, add_left_inj] at h2

private lemma case1_1_lem5 (x y : R) : f (x * y) + 1 = (f x + 1) * (f y + 1) :=
  by rw [add_one_mul, mul_add_one, add_assoc, ← add_assoc (f x),
    ← case1_1_lem4 h h0 h1, ← case1_1_lem3 h h0 h1, ← sub_eq_iff_eq_add, h]

theorem case1_1_sol : ∃ φ : R →+* S, f = λ x, φ x - 1 :=
  ⟨⟨λ x, f x + 1,
      add_left_eq_self.mpr (good_map_one h),
      case1_1_lem5 h h0 h1,
      add_eq_zero_iff_eq_neg.mpr (case1_map_zero h h0),
      λ x y, by rw [case1_1_lem4 h h0 h1, add_add_add_comm, add_assoc]⟩,
    funext (λ x, by rw [ring_hom.coe_mk, add_sub_cancel])⟩

end IMO2012A5
end IMOSL
