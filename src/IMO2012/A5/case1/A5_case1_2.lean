import IMO2012.A5.case1.A5_case1_lemmas data.real.basic

/-! # IMO 2012 A5, Case 1.2: `f(-1) = -1 ≠ 2` -/

namespace IMOSL
namespace IMO2012A5

section lemmas

variables {R S : Type*} [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f 0 = -1) (h1 : f (-1) ≠ 0) (h2 : f (-1) ≠ -2)
include h h0 h1 h2

private lemma case1_2_lem1 : f (-1) = 1 :=
  (case1_map_neg_one_values h h0 h1).resolve_left h2

private lemma case1_2_lem2 (x : R) : f x + f (x + 1) + f (x + 2) = 0 :=
  by rw [case1_map_add_two h h0 h1, case1_2_lem1 h h0 h1 h2,
    mul_neg_one, ← neg_add', add_comm (f x), add_neg_self]

private lemma case1_2_lem3 (x : R) : f (x + 3) = f x :=
  by rw [← add_zero (f x), ← case1_2_lem2 h h0 h1 h2 (x + 1), add_assoc x, ← add_assoc,
    ← add_assoc, ← bit0, case1_2_lem2 h h0 h1 h2, zero_add, bit1, ← add_assoc, add_right_comm]



/-- For now we just obtain a contradiction for `R` a field of characteristic zero. -/
private lemma case1_2_lem4 (x : R) : f (x * 3 + 1) = 0 :=
  by have h3 := h x (0 + 3); rwa [case1_2_lem3 h h0 h1 h2, h0, zero_add,
    case1_2_lem3 h h0 h1 h2, mul_neg_one, sub_eq_neg_self] at h3

end lemmas



/-- The case `R = ℝ` -/
theorem case1_2_real_sol {S : Type*} [ring S] [is_domain S]
  {f : ℝ → S} (h : good f) (h0 : f 0 = -1) (h1 : f (-1) ≠ 0) (h2 : f (-1) ≠ -2) : false :=
  h1 (by rw [← case1_2_lem4 h h0 h1 h2 ((-1 - 1) * 3⁻¹),
    inv_mul_cancel_right₀ (ne_zero.ne (3 : ℝ)), sub_add_cancel])

end IMO2012A5
end IMOSL
