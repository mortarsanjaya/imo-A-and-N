import algebra.ring.regular algebra.hom.ring

/-! # IMO 2012 A5, Basic File -/

namespace IMOSL
namespace IMO2012A5

def good {R S : Type*} [ring R] [ring S] (f : R → S) :=
  ∀ x y : R, f (x * y + 1) - f (x + y) = f x * f y





lemma zero_is_good {R S : Type*} [ring R] [ring S] : good (λ _ : R, (0 : S)) :=
  λ _ _, (sub_self 0).trans (mul_zero 0).symm

lemma good_map_comp_hom {R R0 S : Type*} [ring R] [ring R0] [ring S]
  {f : R → S} (h : good f) (φ : R0 →+* R) : good (f ∘ φ) :=
  λ x y, (congr_arg2 has_sub.sub (congr_arg f $ by rw [φ.map_add, φ.map_mul, φ.map_one])
    (congr_arg f $ φ.map_add x y)).trans (h (φ x) (φ y))

variables {R S : Type*} [ring R] [ring S]

section

variables {f : R → S} (h : good f)
include h

lemma map_comm_of_comm {x y : R} (h0 : commute x y) : commute (f x) (f y) :=
  by have h1 := h y x; rwa [← h0.eq, add_comm y, h] at h1

lemma map_neg_sub_map1 (x : R) : f (1 - x) - f (x - 1) = f x * f (-1) :=
  by rw [← h, mul_neg_one, neg_add_eq_sub, ← sub_eq_add_neg]

lemma map_neg_sub_map2 (x : R) : f (-x) - f x = f (x + 1) * f (-1) :=
  by rw [← map_neg_sub_map1 h, add_sub_cancel, ← sub_sub, sub_sub_cancel_left]

end



section domain

variables [is_domain S] {f : R → S} (h : good f)
include h

lemma good_map_one : f 1 = 0 :=
  by replace h := h 1 1; rwa [mul_one, sub_self, zero_eq_mul_self] at h

lemma eq_zero_of_map_zero_ne_neg_one (h0 : f 0 ≠ -1) : f = λ _, 0 :=
  funext (λ x, by have h1 := h x 0; rwa [mul_zero, zero_add, good_map_one h, zero_sub,
    add_zero, ← mul_neg_one, mul_eq_mul_left_iff, or_iff_right h0.symm] at h1)

end domain

end IMO2012A5
end IMOSL
