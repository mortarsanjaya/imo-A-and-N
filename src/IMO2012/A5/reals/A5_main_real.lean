import IMO2012.A5.case1.A5_case1_sol IMO2012.A5.reals.A5_case2_real

namespace IMOSL
namespace IMO2012A5

instance : is_empty (ℝ →+* 𝔽₃) :=
  ⟨λ φ, begin
    have h0 := congr_arg φ (mul_inv_cancel (three_ne_zero : (3 : ℝ) ≠ 0)),
    rw [φ.map_mul, φ.map_bit1, φ.map_one] at h0,
    exact 𝔽₃.no_confusion h0
  end⟩

theorem final_solution_real {S : Type*} [comm_ring S] [is_domain S] {f : ℝ → S} :
  good f ↔ (f = λ _, 0) ∨ (∃ φ : ℝ →+* S, f = λ x, φ x ^ 2 - 1) ∨
    (∃ φ : ℝ →+* S, f = λ x, φ x - 1) :=
  ⟨λ h, (ne_or_eq (f 0) (-1)).imp (eq_zero_of_map_zero_ne_neg_one h) $
    λ h0, (eq_or_ne (f $ -1) 0).imp (case2_real_sol h h0) $
      λ h1, (case1_sol h h1).resolve_right is_empty.exists_iff.mp,
  λ h, begin
    rcases h with rfl | ⟨φ, rfl⟩ | ⟨φ, rfl⟩,
    exacts [zero_is_good, good_map_comp_hom case2_real_answer φ,
      good_map_comp_hom sub_one_is_good φ]
  end⟩

end IMO2012A5
end IMOSL
