import
  IMO2012.A5.case2.A5_case2_lemmas
  IMO2012.A5.A5_period_quot
  IMO2012.A5.explicit_rings.Z4

/-! # IMO 2012 A5, Case 2.2: `f(2) = 1 ≠ 3` -/

namespace IMOSL
namespace IMO2012A5

def ℤ₄_map (R : Type*) [ring R] : ℤ₄ → R
| ℤ₄.ℤ₄0 := -1
| ℤ₄.ℤ₄1 := 0
| ℤ₄.ℤ₄2 := 1
| ℤ₄.ℤ₄3 := 0

/-- The respective solution for the subcase. -/
theorem case2_2_answer (R : Type*) [ring R] : good (ℤ₄_map R)
| ℤ₄.ℤ₄0 x := (zero_sub _).trans (neg_one_mul _).symm
| ℤ₄.ℤ₄1 x := (sub_eq_zero_of_eq $ congr_arg (ℤ₄_map R) $
    add_comm _ _).trans (zero_mul _).symm
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄0 := (zero_sub 1).trans (one_mul (-1)).symm
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄1 := (sub_self 0).trans (mul_zero 1).symm
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄2 := (zero_sub (-1)).trans $ (neg_neg 1).trans (mul_one 1).symm
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄3 := (sub_self 0).trans (mul_zero 1).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄0 := (sub_self 0).trans (zero_mul (-1)).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄1 := (sub_self (-1)).trans (zero_mul 0).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄2 := (sub_self 0).trans (zero_mul 1).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄3 := (sub_self 1).trans (zero_mul 0).symm





section noncomm_ring

variables {R S : Type*} [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f 2 = 1)
include h h0

private lemma case2_2_lem1 (x : R) : f (x * 2 + 1) = f x + f (x + 2) :=
  by rw [map_mul_two_add_one h, h0, mul_one]

variables (h1 : f (-1) = 0) 
include h1

private lemma case2_2_lem2 (x : R) : f x + f (x + 2) = f (x - 1) + f (x + 1) :=
  by rw [case2_map_add_two_eq h h1, h0, mul_one,
    ← add_sub_right_comm, add_sub_cancel'_right, add_comm]

private lemma case2_2_lem3 (x : R) : f ((x - 1) * 2 + 1) = f (x * 2 + 1) :=
  by rw [case2_2_lem1 h h0, bit0, sub_add_add_cancel,
    ← case2_2_lem2 h h0 h1, ← case2_2_lem1 h h0, ← bit0]

variable (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h2

private lemma case2_2_lem4 : (4 : R) = 0 :=
  h2 4 $ λ x, by rw [add_comm, ← add_left_inj (f (x + 2)), bit0,
    ← add_assoc, add_comm, case2_2_lem2 h h0 h1, bit0, ← add_assoc,
    add_sub_cancel, add_assoc, ← bit0, case2_2_lem2 h h0 h1, add_sub_cancel]

variable (h3 : f 2 ≠ 3)
include h3

private lemma case2_2_lem5 (x : R) : f (2 * x + 1) = 0 :=
begin
  have h4 := case2_2_lem1 h h0 ((x - 1) * 2 + 1),
  rw [case2_2_lem3 h h0 h1, add_right_comm, sub_one_mul, sub_add_cancel,
      bit0, ← sub_sub, sub_add_cancel, sub_one_mul, ← sub_sub, ← bit0,
      sub_add_cancel, mul_assoc, two_mul, ← bit0, case2_2_lem4 h h0 h1 h2,
      mul_zero, zero_sub, h1, ← two_mul, zero_eq_mul, mul_two, ← two_mul] at h4,
  exact h4.resolve_left (mt add_left_eq_self.mpr $ ne_of_ne_of_eq h3.symm h0)
end

private lemma case2_2_lem6 : f 0 = -1 :=
  not_not.mp $ λ h4, one_ne_zero $ h0.symm.trans $
    congr_fun (eq_zero_of_map_zero_ne_neg_one h h4) 2

private lemma case2_2_lem7 : (2 : R) ≠ 0 :=
  λ h5, h3 $ by rw [h0, bit1, self_eq_add_left, bit0,
    add_eq_zero_iff_neg_eq, ← case2_2_lem6 h h0 h1 h2 h3, ← h0, h5]

end noncomm_ring



section comm_ring

variables {R S : Type*} [comm_ring R] [ring S] [is_domain S] {f : R → S} (h : good f)
  (h0 : f (-1) = 0) (h1 : f 2 = 1) (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h h0 h1 h2

private def case2_2_ℤ₄_hom : ℤ₄ →+* R :=
  ℤ₄.cast_hom (case2_2_lem4 h h1 h0 h2)

variable (h3 : f 2 ≠ 3)
include h3

private lemma case2_2_lem8 (x : R) : (x = 0 ∨ x = 2) ∨ (x = 1 ∨ x = -1) :=
  (cases_of_nonperiod_quasi_period h h2 (case2_2_lem6 h h1 h0 h2 h3)
    (case2_2_lem5 h h1 h0 h2 h3) (case2_2_lem7 h h1 h0 h2 h3) x).imp id $
  or.imp id $ λ h6, by rw [h6, eq_neg_iff_add_eq_zero, add_assoc];
    exact case2_2_lem4 h h1 h0 h2

private lemma case2_2_ℤ₄_hom_bijective :
  function.bijective (case2_2_ℤ₄_hom h h0 h1 h2) :=
  let h4 := case2_2_lem7 h h1 h0 h2 h3 in
  ⟨ℤ₄.cast_hom_injective _ (case2_2_lem7 h h1 h0 h2 h3),
  λ x, (case2_2_lem8 h h0 h1 h2 h3 x).elim
    (λ h5, h5.elim (λ h6, ⟨ℤ₄.ℤ₄0, h6.symm⟩) (λ h6, ⟨ℤ₄.ℤ₄2, h6.symm⟩))
    (λ h5, h5.elim (λ h6, ⟨ℤ₄.ℤ₄1, h6.symm⟩) (λ h6, ⟨ℤ₄.ℤ₄3, h6.symm⟩))⟩

private noncomputable def case2_2_ℤ₄_equiv : ℤ₄ ≃+* R :=
  ring_equiv.of_bijective _ (case2_2_ℤ₄_hom_bijective h h0 h1 h2 h3)

private lemma case2_2_quotient_sol' :
  ∀ x : ℤ₄, f (case2_2_ℤ₄_equiv h h0 h1 h2 h3 x) = ℤ₄_map S x
| ℤ₄.ℤ₄0 := case2_2_lem6 h h1 h0 h2 h3
| ℤ₄.ℤ₄1 := good_map_one h
| ℤ₄.ℤ₄2 := h1
| ℤ₄.ℤ₄3 := h0

private lemma case2_2_quotient_sol : f = ℤ₄_map S ∘ (case2_2_ℤ₄_equiv h h0 h1 h2 h3).symm :=
  funext $ λ x, (congr_arg f ((case2_2_ℤ₄_equiv h h0 h1 h2 h3).apply_symm_apply x).symm).trans $
    case2_2_quotient_sol' h h0 h1 h2 h3 $ (case2_2_ℤ₄_equiv h h0 h1 h2 h3).symm x

end comm_ring



section solution

variables {R S : Type*} [comm_ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 1) (h2 : f 2 ≠ 3)
include h h0 h1 h2

private lemma case2_2_lift_decomp :
  ∃ φ : R ⧸ period_ideal h ≃+* ℤ₄, period_lift h = ℤ₄_map S ∘ φ :=
  ⟨_, case2_2_quotient_sol (period_lift_is_good h) h0 h1 (zero_of_periodic_period_lift h) h2⟩

theorem case2_2_sol : ∃ φ : R →+* ℤ₄, function.surjective φ ∧ f = ℤ₄_map S ∘ φ :=
  exists.elim (case2_2_lift_decomp h h0 h1 h2) $ λ ψ h2,
    ⟨ψ.to_ring_hom.comp $ ideal.quotient.mk (period_ideal h),
    (equiv_like.surjective ψ).comp (ideal.quotient.mk $ period_ideal h).is_surjective,
    (period_lift_comp_quotient_eq_f h).symm.trans $
      congr_arg (λ u, u ∘ ideal.quotient.mk (period_ideal h)) h2⟩

end solution

end IMO2012A5
end IMOSL
