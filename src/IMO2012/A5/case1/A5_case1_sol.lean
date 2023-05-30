import
  IMO2012.A5.case1.A5_case1_lemmas
  IMO2012.A5.case1.A5_case1_1
  IMO2012.A5.case1.A5_case1_2

/-! # IMO 2012 A5, Full Solution for Case 1: `f(-1) ≠ 0` -/

namespace IMOSL
namespace IMO2012A5

variables {R S : Type*}

lemma case1_map_neg_one_values [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) : f (-1) = -2 ∨ f (-1) = 1 :=
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

theorem case1_sol [comm_ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) :
    (∃ φ : R →+* S, f = λ x, φ x - 1) ∨
    (∃ φ : R →+* 𝔽₃, function.surjective φ ∧ f = 𝔽₃_map1 S ∘ φ) :=
  (eq_or_ne (f $ -1) (-2)).imp (case1_1_sol h h0) $
    λ h1, case1_2_sol h ((case1_map_neg_one_values h h0).resolve_left h1) h1

end IMO2012A5
end IMOSL
