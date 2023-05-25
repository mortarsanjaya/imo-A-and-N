import
  IMO2012.A5.case2.A5_case2_lemmas
  IMO2012.A5.A5_period_quot
  IMO2012.A5.explicit_rings.F2
  IMO2012.A5.explicit_rings.F4
  algebra.dual_number

/-! # IMO 2012 A5, Case 2.3: `f(2) = -1 ≠ 3` -/

namespace IMOSL
namespace IMO2012A5

section answers

variables (R : Type*) [ring R]

def 𝔽₂_map : 𝔽₂ → R
| 𝔽₂.O := -1
| 𝔽₂.I := 0

/-- The first respective solution for the subcase. -/
theorem case2_3_answer1 : good (𝔽₂_map R)
| 𝔽₂.O x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₂.I x := (sub_eq_zero_of_eq $ congr_arg (𝔽₂_map R) $
    add_comm _ _).trans (zero_mul _).symm

def 𝔽₄_map (φ : R) : 𝔽₄ → R
| 𝔽₄.O := -1
| 𝔽₄.I := 0
| 𝔽₄.X := φ
| 𝔽₄.Y := 1 - φ

/-- The second respective solution for the subcase. -/
theorem case2_3_answer2 {φ : R} (h : φ * (1 - φ) = -1) : good (𝔽₄_map R φ)
| 𝔽₄.O x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₄.I x := (sub_eq_zero_of_eq $ congr_arg (𝔽₄_map R φ) $
    add_comm _ _).trans (zero_mul _).symm
| 𝔽₄.X 𝔽₄.O := (zero_sub φ).trans (mul_neg_one φ).symm
| 𝔽₄.X 𝔽₄.I := (sub_self _).trans (mul_zero φ).symm
| 𝔽₄.X 𝔽₄.X := sub_eq_of_eq_add $ eq_add_of_sub_eq' $ (mul_one_sub φ φ).symm.trans h
| 𝔽₄.X 𝔽₄.Y := (sub_zero (-1)).trans h.symm
| 𝔽₄.Y 𝔽₄.O := (zero_sub _).trans (mul_neg_one _).symm
| 𝔽₄.Y 𝔽₄.I := (sub_self φ).trans (mul_zero _).symm
| 𝔽₄.Y 𝔽₄.X := (sub_zero (-1)).trans $ h.symm.trans $
    (mul_one_sub φ φ).trans (one_sub_mul φ φ).symm
| 𝔽₄.Y 𝔽₄.Y := sub_eq_of_eq_add $ eq_add_of_sub_eq' $
  (one_sub_mul _ _).symm.trans $ (congr_arg (* (1 - φ)) (sub_sub_cancel 1 φ)).trans h

def 𝔽₂ε_map : dual_number 𝔽₂ → R
| (𝔽₂.O, 𝔽₂.O) := -1
| (𝔽₂.O, 𝔽₂.I) := 1
| (𝔽₂.I, _) := 0

/-- The third respective solution for the subcase. -/
theorem case2_3_answer3 : good (𝔽₂ε_map R)
| (𝔽₂.O, 𝔽₂.O) (x, y) := (zero_sub _).trans (neg_one_mul _).symm
| (𝔽₂.O, 𝔽₂.I) (𝔽₂.O, 𝔽₂.O) := (zero_sub 1).trans (one_mul (-1)).symm
| (𝔽₂.O, 𝔽₂.I) (𝔽₂.O, 𝔽₂.I) := (zero_sub (-1)).trans $ (neg_neg 1).trans (one_mul 1).symm
| (𝔽₂.O, 𝔽₂.I) (𝔽₂.I, y) := (sub_self 0).trans (one_mul 0).symm
| (𝔽₂.I, b) (𝔽₂.O, y) := (sub_self 0).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.O) (𝔽₂.I, 𝔽₂.O) := (sub_self _).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.O) (𝔽₂.I, 𝔽₂.I) := (sub_self _).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.I) (𝔽₂.I, 𝔽₂.O) := (sub_self _).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.I) (𝔽₂.I, 𝔽₂.I) := (sub_self _).trans (zero_mul _).symm

end answers



section noncomm_ring

variables {R S : Type*} [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = -1)
include h h0 h1

/- Nothing yet -/

end noncomm_ring



section solution

variables {R S : Type*} [comm_ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = -1) (h2 : f 2 ≠ 3)
include h h0 h1 h2

/- Nothing yet -/

end solution

end IMO2012A5
end IMOSL
