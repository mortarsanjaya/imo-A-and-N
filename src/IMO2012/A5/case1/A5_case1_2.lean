import
  IMO2012.A5.case1.A5_case1_lemmas
  IMO2012.A5.A5_period_quot
  IMO2012.A5.explicit_rings.F3

/-! # IMO 2012 A5, Case 1.2: `f(-1) = -1 ≠ 2` -/

namespace IMOSL
namespace IMO2012A5

def 𝔽₃_map1 (R : Type*) [ring R] : 𝔽₃ → R
| 𝔽₃.𝔽₃0 := -1
| 𝔽₃.𝔽₃1 := 0
| 𝔽₃.𝔽₃2 := 1

/-- The respective solution for the subcase. -/
theorem case1_2_answer (R : Type*) [ring R] : good (𝔽₃_map1 R)
| 𝔽₃.𝔽₃0 𝔽₃.𝔽₃0 := (zero_sub (-1)).trans (mul_neg_one (-1)).symm
| 𝔽₃.𝔽₃0 𝔽₃.𝔽₃1 := (sub_self 0).trans (mul_zero (-1)).symm 
| 𝔽₃.𝔽₃0 𝔽₃.𝔽₃2 := (zero_sub 1).trans (neg_one_mul 1).symm
| 𝔽₃.𝔽₃1 𝔽₃.𝔽₃0 := (sub_self 0).trans (zero_mul (-1)).symm
| 𝔽₃.𝔽₃1 𝔽₃.𝔽₃1 := (sub_self 1).trans (zero_mul 0).symm
| 𝔽₃.𝔽₃1 𝔽₃.𝔽₃2 := (sub_self (-1)).trans (zero_mul 1).symm
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃0 := (zero_sub 1).trans (mul_neg_one 1).symm
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃1 := (sub_self (-1)).trans (mul_zero 1).symm 
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃2 := (sub_zero 1).trans (mul_one 1).symm





section noncomm_ring

variables {R S : Type*} [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f 0 = -1) (h1 : f (-1) ≠ 0) (h2 : f (-1) ≠ -2)
include h h0 h1 h2

private lemma case1_2_lem1 : f (-1) = 1 :=
  (case1_map_neg_one_values h h0 h1).resolve_left h2

private lemma case1_2_lem2 : (1 : R) ≠ 0 :=
  mt (congr_arg f) $ ne_of_eq_of_ne (good_map_one h) $
    ne_of_ne_of_eq (neg_ne_zero.mpr one_ne_zero).symm h0.symm



variable (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h3

private lemma case1_2_lem3 {c : R} (h4 : f (c + 1) = 0) : c = 0 :=
  h3 c $ λ x,
begin
  have h5 := (case1_map_eq_zero_imp h h0 h1 h4).2,
  rw [← neg_inj, ← case1_map_neg_add_one h h0 h1, neg_zero] at h4,
  replace h4 := (case1_map_eq_zero_imp h h0 h1 h4).2,
  rw add_sub_cancel at h4 h5,
  have h6 := case1_map_add_main_equality h (x - 1) c,
  rwa [h4, h5, ← sub_mul, neg_sub, map_neg_sub_map1 h, mul_neg_one,
       neg_mul, neg_inj, mul_eq_mul_right_iff, or_iff_left h1,
       ← add_sub_right_comm, sub_add_cancel, add_comm] at h6
end

private lemma case1_2_lem4 {c : R} : f (c + 1) = 0 ↔ c = 0 :=
  ⟨case1_2_lem3 h h0 h1 h2 h3, λ h4, by rw [h4, zero_add]; exact good_map_one h⟩

private lemma case1_2_lem5 : (3 : R) = 0 :=
  case1_2_lem3 h h0 h1 h2 h3 $ by rw [bit1, add_assoc, ← bit0, case1_map_add_two h h0 h1,
    add_comm, case1_map_add_two h h0 h1, case1_2_lem1 h h0 h1 h2, good_map_one h,
    sub_zero, mul_neg_one, mul_neg_one, neg_neg]; exact sub_self (f 2)

private lemma case1_2_lem6 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 :=
begin
  by_contra' h4; rcases h4 with ⟨h4, h5, h6⟩,
  rw [← sub_eq_zero, ← case1_2_lem4 h h0 h1 h2 h3] at h4 h5 h6,
  rw sub_zero at h4; replace h4 := case1_map_ne_zero_imp h h0 h1 h4,
  rw sub_add_cancel at h5; replace h5 := case1_map_ne_zero_imp h h0 h1 h5,
  rw sub_neg_eq_add at h6; replace h6 := case1_map_ne_zero_imp h h0 h1 h6,
  rw add_sub_cancel at h6,
  rw [add_sub_cancel, ← add_sub_cancel (x + 1 + 1) 1] at h4,
  rw [add_assoc x, add_assoc, ← bit0, ← bit1, case1_2_lem5 h h0 h1 h2 h3, add_zero] at h4 h6,
  replace h3 := congr_arg2 has_add.add (congr_arg2 has_add.add h4 h5) h6,
  rw [sub_add_sub_cancel, sub_add_sub_cancel, sub_self, ← two_mul, ← add_one_mul] at h3,
  revert h3; refine (mul_ne_zero _ h1).symm,
  rw [ne.def, add_eq_zero_iff_neg_eq],
  exact ne_of_ne_of_eq h2.symm (case1_2_lem1 h h0 h1 h2)
end



private def case1_2_𝔽₃_hom : 𝔽₃ →+* R :=
  𝔽₃.cast_hom (case1_2_lem5 h h0 h1 h2 h3)

private lemma case1_2_𝔽₃_hom_bijective :
  function.bijective (case1_2_𝔽₃_hom h h0 h1 h2 h3) :=
  ⟨𝔽₃.cast_hom_injective _ (case1_2_lem2 h h0 h1 h2),
  λ x, (case1_2_lem6 h h0 h1 h2 h3 x).elim (λ h4, ⟨𝔽₃.𝔽₃0, h4.symm⟩) $
    λ h4, h4.elim (λ h5, ⟨𝔽₃.𝔽₃1, h5.symm⟩) (λ h5, ⟨𝔽₃.𝔽₃2, h5.symm⟩)⟩

private noncomputable def case1_2_𝔽₃_equiv : 𝔽₃ ≃+* R :=
  ring_equiv.of_bijective _ (case1_2_𝔽₃_hom_bijective h h0 h1 h2 h3)

private lemma case1_2_quotient_sol' :
  ∀ x : 𝔽₃, f (case1_2_𝔽₃_equiv h h0 h1 h2 h3 x) = 𝔽₃_map1 S x
| 𝔽₃.𝔽₃0 := h0
| 𝔽₃.𝔽₃1 := good_map_one h
| 𝔽₃.𝔽₃2 := case1_2_lem1 h h0 h1 h2

private lemma case1_2_quotient_sol : f = 𝔽₃_map1 S ∘ (case1_2_𝔽₃_equiv h h0 h1 h2 h3).symm :=
  funext $ λ x, (congr_arg f ((case1_2_𝔽₃_equiv h h0 h1 h2 h3).apply_symm_apply x).symm).trans $
    case1_2_quotient_sol' h h0 h1 h2 h3 $ (case1_2_𝔽₃_equiv h h0 h1 h2 h3).symm x

end noncomm_ring



section solution

variables {R S : Type*} [comm_ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f 0 = -1) (h1 : f (-1) ≠ 0) (h2 : f (-1) ≠ -2)
include h h0 h1 h2

private lemma case1_2_lift_decomp :
  ∃ φ : R ⧸ period_ideal h ≃+* 𝔽₃, period_lift h = 𝔽₃_map1 S ∘ φ :=
  ⟨_, case1_2_quotient_sol (period_lift_is_good h) h0 h1 h2 (zero_of_periodic_period_lift h)⟩

theorem case1_2_sol : ∃ φ : R →+* 𝔽₃, f = 𝔽₃_map1 S ∘ φ :=
  exists.elim (case1_2_lift_decomp h h0 h1 h2) $ λ ψ h3,
    ⟨ψ.to_ring_hom.comp $ ideal.quotient.mk (period_ideal h),
    (period_lift_comp_quotient_eq_f h).symm.trans $
      congr_arg (λ u, u ∘ ideal.quotient.mk (period_ideal h)) h3⟩

end solution

end IMO2012A5
end IMOSL
