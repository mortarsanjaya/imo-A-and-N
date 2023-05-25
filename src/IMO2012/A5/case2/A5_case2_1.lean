import
  IMO2012.A5.case2.A5_case2_lemmas
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

variables {R S : Type*} [ring R] [ring S] [is_domain S] {f : R → S} (h : good f)
  (h0 : f (-1) = 0) (h1 : f 2 = 0) (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h h0 h1 h2

private lemma case2_1_lem1 : (3 : R) = 0 :=
  h2 3 $ λ x, begin end

end noncomm_ring



section solution

variables {R S : Type*} [comm_ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 0) (h2 : f 2 ≠ 3)
include h h0 h1 h2

theorem case2_1_sol : ∃ φ : R →+* 𝔽₃, function.surjective φ ∧ f = 𝔽₃_map2 S ∘ φ :=
  sorry

end solution

end IMO2012A5
end IMOSL
