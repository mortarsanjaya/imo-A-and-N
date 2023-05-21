import algebra.hom.ring algebra.ring.regular

/-! # IMO 2012 A5, Basic File -/

namespace IMOSL
namespace IMO2012A5

def good {R S : Type*} [ring R] [ring S] (f : R → S) :=
  ∀ x y : R, f (x * y + 1) - f (x + y) = f x * f y





/-- The zero map is always good. -/
lemma zero_is_good {R S : Type*} [ring R] [ring S] : good (λ _ : R, (0 : S)) :=
  λ _ _, (sub_self 0).trans (mul_zero 0).symm


section hom

variables {R R₀ S : Type*} [ring R] [ring R₀] [ring S]

/-- Given `f : R → S` good and `φ : R₀ →+* R`, `f ∘ φ` is good as well. -/
lemma good_map_comp_hom {f : R → S} (h : good f) (φ : R₀ →+* R) : good (f ∘ φ) :=
  λ x y, (congr_arg2 (λ u v, f v - f u) (φ.map_add x y) $
    (φ.map_add _ _).trans $ congr_arg2 has_add.add (φ.map_mul x y) φ.map_one).trans $
      h (φ x) (φ y)

/-- Given `f : R → S` and `φ : R₀ →+* R`, `f` is good if `φ` is surjective and `f ∘ φ` is good. -/
lemma good_of_comp_hom_good_surjective {φ : R₀ →+* R} (h : function.surjective φ)
  {f : R → S} (h0 : good (f ∘ φ)) : good f :=
  λ x y, exists.elim (h x) $ λ a h1, exists.elim (h y) $ λ b h2,
    by rw [← h1, ← h2, ← φ.map_mul, ← φ.map_add, ← φ.map_one, ← φ.map_add, h0 a b]

end hom


section non_domain

variables {R S : Type*} [ring R] [ring S] {f : R → S} (h : good f)
include h

lemma map_comm_of_comm {x y : R} (h0 : commute x y) : commute (f x) (f y) :=
  (h x y).symm.trans $ (congr_arg2 (λ u v, f (u + 1) - f v) h0 (add_comm x y)).trans (h y x)

lemma map_neg_sub_map1 (x : R) : f (1 - x) - f (x - 1) = f x * f (-1) :=
  (congr_arg2 (λ u v, f v - f u) (sub_eq_add_neg x 1)
    ((congr_arg (λ u : R, u + 1) $ mul_neg_one x).trans $ neg_add_eq_sub x 1).symm).trans $
  h x (-1)

lemma map_neg_sub_map2 (x : R) : f (-x) - f x = f (x + 1) * f (-1) :=
  (congr_arg2 (λ u v, f v - f u) (add_sub_cancel x 1).symm
    ((sub_add_cancel' 1 x).symm.trans $ congr_arg (has_sub.sub 1) (add_comm 1 x))).trans $
  map_neg_sub_map1 h $ x + 1

lemma map_mul_two_add_one (x : R) : f (x * 2 + 1) = f x * f 2 + f (x + 2) :=
  eq_add_of_sub_eq (h x 2)

end non_domain


section domain

variables {R S : Type*} [ring R] [ring S] [is_domain S] {f : R → S} (h : good f)
include h

lemma good_map_one : f 1 = 0 :=
  mul_self_eq_zero.mp $ (h 1 1).symm.trans $ sub_eq_zero.mpr $
    congr_arg f $ (add_left_inj 1).mpr (mul_one 1)

lemma eq_zero_of_map_zero_ne_neg_one (h0 : f 0 ≠ -1) : f = λ _, 0 :=
  funext $ λ x, by have h1 := h x 0; rwa [mul_zero, zero_add, good_map_one h, zero_sub,
    add_zero, ← mul_neg_one, mul_eq_mul_left_iff, or_iff_right h0.symm] at h1

end domain

end IMO2012A5
end IMOSL
