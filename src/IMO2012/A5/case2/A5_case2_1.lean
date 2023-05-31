import
  IMO2012.A5.case2.A5_case2_general
  IMO2012.A5.case2.A5_case2_comm
  IMO2012.A5.A5_period_quot
  IMO2012.A5.explicit_rings.F3

/-! # IMO 2012 A5, Case 2.1: `f(2) = 0 ≠ 3` -/

namespace IMOSL
namespace IMO2012A5

def 𝔽₃_map2 (R : Type*) [ring R] : 𝔽₃ → R
| 𝔽₃.𝔽₃0 := -1
| 𝔽₃.𝔽₃1 := 0
| 𝔽₃.𝔽₃2 := 0

/-- The respective solution for the subcase. -/
theorem case2_1_answer (R : Type*) [ring R] : good (𝔽₃_map2 R)
| 𝔽₃.𝔽₃0 x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₃.𝔽₃1 x := (sub_eq_zero_of_eq $ congr_arg (𝔽₃_map2 R) $
    add_comm _ _).trans (zero_mul _).symm
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃0 := (sub_self 0).trans (zero_mul (-1)).symm
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃1 := (sub_self (-1)).trans (mul_zero 0).symm 
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃2 := (sub_zero 0).trans (mul_zero 0).symm





section noncomm_ring

variables {R S : Type*} [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)
include h h0

private lemma case2_1_lem1 (h1 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (h2 : f 2 = 0) :
  (3 : R) = 0 :=
  h1 3 $ λ x, by rw [add_comm, bit1, ← add_assoc, add_right_comm,
    case2_map_add_two_eq h h0, h2, mul_zero, zero_add, add_sub_cancel]

variable (h1 : (3 : R) = 0)
include h1

private def case2_1_𝔽₃_hom : 𝔽₃ →+* R :=
  𝔽₃.cast_hom h1



private lemma case2_1_lem2 (x : R) : f x * f (x + 1) = (f (x - 1) + 1) * f (x - 1) :=
  by rw [eq_add_of_sub_eq' (case2_special_identity h h0 x), eq_neg_of_add_eq_zero_left h1,
    h0, mul_zero, zero_add, ← sub_eq_add_neg, add_one_mul]

private lemma case2_1_lem3 (x : R) : f (x + 1) * f (x - 1) = (f x + 1) * f x :=
  by rw [sub_eq_add_neg, ← eq_neg_of_add_eq_zero_left h1,
    bit0, ← add_assoc, case2_1_lem2 h h0 h1, add_sub_cancel]

private lemma case2_1_lem4 (x : R) :
  f (x + 1) = f (x - 1) ∨ f x + (f (x + 1) + f (x - 1)) = -1 :=
begin
  /- This code is a slow; it takes nearly 0.2s -/
  have h2 := case2_map_is_even h h0,
  have h3 := case2_1_lem2 h h0 h1 (-x),
  rw [h2, ← neg_add', h2, ← sub_neg_eq_add, ← neg_sub', h2] at h3,
  replace h3 := congr_arg2 has_sub.sub h3 (case2_1_lem2 h h0 h1 x),
  rw [← mul_sub, add_one_mul, add_one_mul, add_sub_add_comm, ← neg_sub, ← neg_mul_comm,  
      (map_comm_of_comm h $ comm_add_one_sub_one x).mul_self_sub_mul_self_eq,
      ← add_one_mul, mul_eq_mul_right_iff] at h3,
  refine h3.symm.imp eq_of_sub_eq_zero (λ h4, _),
  rwa [eq_neg_iff_add_eq_zero, add_assoc, ← neg_eq_iff_add_eq_zero]
end

variable (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h2

private lemma case2_1_lem5 {c : R} (h3 : f (c + 1) = 0) (h4 : f (c - 1) = 0) : c = 0 :=
  /- This code is slow; it takes about 0.3s -/
  h2 c $ λ y, let z := y + (c + c) - 1 in by replace h2 := h ((z - 1) * (c - 1)) (c + 1);
  rwa [h3, mul_zero, mul_assoc, (comm_add_one_sub_one c).symm.eq, ← mul_assoc, sub_eq_zero,
    eq_add_of_sub_eq (h _ _), h4, mul_zero, zero_add, sub_one_mul z, sub_one_mul z,
    sub_add, sub_add, add_sub_sub_cancel, sub_right_comm, sub_add_cancel',
    ← neg_add', ← bit0, eq_neg_of_add_eq_zero_left h1, neg_neg, sub_neg_eq_add,
    eq_add_of_sub_eq (h _ _), eq_add_of_sub_eq (case2_good_alt h h0 _ _), h3, h4,
    mul_zero, zero_add, zero_add, ← sub_add, ← add_assoc, ← add_sub_right_comm z,
    add_right_comm, sub_add_cancel, add_assoc, ← add_assoc y c c, add_sub_cancel,
    ← two_mul, ← add_one_mul, ← bit1, h1, zero_mul, add_zero, add_comm, eq_comm] at h2

variable (h3 : f 0 = -1)
include h3

private lemma case2_1_lem6 (x : R) : f x + (f (x + 1) + f (x - 1)) = -1 :=
  (case2_1_lem4 h h0 h1 x).symm.elim id $ λ h4,
begin
  have h5 := (case2_1_lem4 h h0 h1 (x + 1)).symm,
  rw [add_sub_cancel, add_assoc, ← bit0, eq_neg_of_add_eq_zero_left h1,
      ← sub_eq_add_neg, ← add_assoc, add_comm] at h5,
  refine h5.resolve_right (λ h6, _),
  replace h5 := case2_1_lem2 h h0 h1 x,
  rw [h4, h6, add_one_mul, self_eq_add_right] at h5,
  rw h5 at h6,
  replace h6 := case2_1_lem5 h h0 h1 h2 (h4.trans h6) h6,
  rw [h6, h3, neg_eq_zero] at h5,
  exact one_ne_zero h5
end

variable (h4 : f 2 ≠ 3)
include h4

private lemma case2_1_lem7 (x : R) : f x = -1 ∨ f x = 0 :=
begin
  /- This code is slow; it takes about 0.2s -/
  rw [eq_neg_of_add_eq_zero_left h1, h0] at h4,
  have h5 := h (x + 1) (x - 1),
  rw [add_add_sub_cancel, case2_1_lem3 h h0 h1, add_one_mul, mul_sub_one,
      sub_add_sub_cancel, sub_add_cancel, sub_eq_iff_eq_add] at h5,
  have h6 := case2_1_lem6 h h0 h1 h2 h3 (x * x),
  rw [eq_add_of_sub_eq (h x x), eq_add_of_sub_eq (case2_good_alt h h0 x x), h5,
      sub_self, h3, ← two_mul, eq_neg_of_add_eq_zero_left h1, neg_one_mul,
      case2_map_is_even h h0, ← add_one_mul, ← add_one_mul, ← add_assoc,
      ← add_mul, ← add_assoc, add_left_eq_self, ← add_mul, mul_eq_zero] at h6,
  refine h6.imp (λ h7, _) id,
  rw [add_right_comm _ (1 : S), ← two_mul, add_right_comm, add_assoc,
      ← add_one_mul, ← bit1, mul_eq_zero, add_eq_zero_iff_eq_neg] at h7,
  exact h7.resolve_left h4.symm
end

private lemma case2_1_lem8 (x : R) (h5 : f x = -1) : x = 0 :=
begin
  replace h4 := case2_1_lem7 h h0 h1 h2 h3 h4,
  replace h3 := case2_1_lem6 h h0 h1 h2 h3 x,
  rw [h5, add_right_eq_self] at h3,
  cases h4 (x + 1) with h6 h6; cases h4 (x - 1) with h7 h7,
  { replace h3 := case2_1_lem3 h h0 h1 x,
    rw [h6, h7, h5, add_one_mul, self_eq_add_right, neg_eq_zero] at h3,
    exact absurd h3 one_ne_zero },
  { rw [h6, h7, add_zero, neg_eq_zero] at h3,
    exact absurd h3 one_ne_zero },
  { rw [h6, h7, zero_add, neg_eq_zero] at h3,
    exact absurd h3 one_ne_zero },
  { exact case2_1_lem5 h h0 h1 h2 h6 h7 }
end

private lemma case2_1_lem9 (x : R) : x = 0 ∨ (x = -1 ∨ x = 1) :=
  let h5 := case2_1_lem7 h h0 h1 h2 h3 h4, h6 := case2_1_lem8 h h0 h1 h2 h3 h4 in
  (h5 x).imp (h6 x) $ λ h7, (h5 $ x + 1).imp
    (λ h8, eq_neg_of_add_eq_zero_left $ h6 (x + 1) h8)
    (λ h8, eq_of_sub_eq_zero $ h6 (x - 1) $
      by rw [← case2_1_lem6 h h0 h1 h2 h3 x, h7, h8, zero_add, zero_add])



private lemma case2_1_𝔽₃_hom_bijective :
  function.bijective (case2_1_𝔽₃_hom h h0 h1) :=
  ⟨𝔽₃.cast_hom_injective _ (one_ne_zero_of_map_zero h h3),
  λ x, (case2_1_lem9 h h0 h1 h2 h3 h4 x).elim (λ h5, ⟨𝔽₃.𝔽₃0, h5.symm⟩) $
    λ h5, h5.elim (λ h6, ⟨𝔽₃.𝔽₃2, h6.symm⟩) (λ h6, ⟨𝔽₃.𝔽₃1, h6.symm⟩)⟩

private noncomputable def case2_1_𝔽₃_equiv : 𝔽₃ ≃+* R :=
  ring_equiv.of_bijective _ (case2_1_𝔽₃_hom_bijective h h0 h1 h2 h3 h4)

private lemma case2_1_quotient_sol' :
  ∀ x : 𝔽₃, f (case2_1_𝔽₃_equiv h h0 h1 h2 h3 h4 x) = 𝔽₃_map2 S x
| 𝔽₃.𝔽₃0 := h3
| 𝔽₃.𝔽₃1 := good_map_one h
| 𝔽₃.𝔽₃2 := h0

private lemma case2_1_quotient_sol : f = 𝔽₃_map2 S ∘ (case2_1_𝔽₃_equiv h h0 h1 h2 h3 h4).symm :=
  let φ := case2_1_𝔽₃_equiv h h0 h1 h2 h3 h4 in
  funext $ λ x, (congr_arg f (φ.apply_symm_apply x).symm).trans $
    case2_1_quotient_sol' h h0 h1 h2 h3 h4 $ φ.symm x

end noncomm_ring



section solution

variables {R S : Type*} [comm_ring R] [ring S] [is_domain S] {f : R → S}
  (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 0) (h2 : f 2 ≠ 3) (h3 : f 0 = -1)
include h h0 h1 h2 h3

private lemma case2_1_lift_decomp :
  ∃ φ : R ⧸ period_ideal h ≃+* 𝔽₃, period_lift h = 𝔽₃_map2 S ∘ φ :=
  let h4 := zero_of_periodic_period_lift h, h5 := period_lift_is_good h in
  ⟨_, case2_1_quotient_sol h5 h0 (case2_1_lem1 h5 h0 h4 h1) h4 h3 h2⟩

theorem case2_1_sol : ∃ φ : R →+* 𝔽₃, function.surjective φ ∧ f = 𝔽₃_map2 S ∘ φ :=
  exists.elim (case2_1_lift_decomp h h0 h1 h2 h3) $
    λ ψ h4, let π := ideal.quotient.mk (period_ideal h) in
    ⟨ψ.to_ring_hom.comp π, (equiv_like.surjective ψ).comp π.is_surjective,
      (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h4⟩

end solution

end IMO2012A5
end IMOSL
