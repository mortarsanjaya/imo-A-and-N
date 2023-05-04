import algebra.ring.regular ring_theory.congruence

/-! # IMO 2012 A5, Basic File -/

namespace IMOSL
namespace IMO2012A5

def good {R S : Type*} [ring R] [ring S] (f : R → S) :=
  ∀ x y : R, f (x * y + 1) - f (x + y) = f x * f y





/-- The zero map is always good. -/
lemma zero_is_good {R S : Type*} [ring R] [ring S] : good (λ _ : R, (0 : S)) :=
  λ _ _, (sub_self 0).trans (mul_zero 0).symm

/-- Given `f : R → S` good and `φ : R₀ →+* R`, `f ∘ φ` is good as well. -/
lemma good_map_comp_hom {R R₀ S : Type*} [ring R] [ring R₀] [ring S]
  {f : R → S} (h : good f) (φ : R₀ →+* R) : good (f ∘ φ) :=
  λ x y, (congr_arg2 (λ u v, f v - f u) (φ.map_add x y) $
    (φ.map_add _ _).trans $ congr_arg2 has_add.add (φ.map_mul x y) φ.map_one).trans
      (h (φ x) (φ y))

/-- An auxiliary definition to state the next lemma. -/
def ring_con_lift {R S : Type*} [ring R] [ring S] {f : R → S} {c : ring_con R}
  (h0 : ∀ x y : R, c x y → f x = f y) : c.quotient → S := 
  quot.lift f h0

/-- Given `f : R → S` good and a ring congruence `∼` on `R` such that `x ∼ y`
  implies `f(x) = f(y)`, the induced map `R/∼ → S` is also good. -/
lemma good_ring_con_lift {R S : Type*} [ring R] [ring S] {f : R → S} (h : good f)
  {c : ring_con R} (h0 : ∀ x y : R, c x y → f x = f y) : good (ring_con_lift h0) :=
  λ x y, quot.induction_on₂ x y h

variables {R S : Type*} [ring R] [ring S]

section non_domain

variables {f : R → S} (h : good f)
include h

lemma map_comm_of_comm {x y : R} (h0 : commute x y) : commute (f x) (f y) :=
  (h x y).symm.trans $ (congr_arg2 (λ u v, f (u + 1) - f v) h0 (add_comm x y)).trans (h y x)

lemma map_neg_sub_map1 (x : R) : f (1 - x) - f (x - 1) = f x * f (-1) :=
  (congr_arg2 (λ u v, f v - f u) (sub_eq_add_neg x 1)
    ((congr_arg (λ u : R, u + 1) $ mul_neg_one x).trans $ neg_add_eq_sub x 1).symm).trans
  (h x (-1))

lemma map_neg_sub_map2 (x : R) : f (-x) - f x = f (x + 1) * f (-1) :=
  (congr_arg2 (λ u v, f v - f u) (add_sub_cancel x 1).symm
    ((sub_add_cancel' 1 x).symm.trans $ congr_arg (has_sub.sub 1) (add_comm 1 x))).trans
  (map_neg_sub_map1 h $ x + 1)

end non_domain

section domain

variables [is_domain S] {f : R → S} (h : good f)
include h

lemma good_map_one : f 1 = 0 :=
  mul_self_eq_zero.mp $ (h 1 1).symm.trans $ sub_eq_zero.mpr $
    congr_arg f $ (add_left_inj 1).mpr (mul_one 1)

lemma eq_zero_of_map_zero_ne_neg_one (h0 : f 0 ≠ -1) : f = λ _, 0 :=
  funext (λ x, by have h1 := h x 0; rwa [mul_zero, zero_add, good_map_one h, zero_sub,
    add_zero, ← mul_neg_one, mul_eq_mul_left_iff, or_iff_right h0.symm] at h1)

end domain

end IMO2012A5
end IMOSL
