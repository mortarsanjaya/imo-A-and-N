import
  IMO2012.A5.case1.A5_case1_1
  IMO2012.A5.case1.A5_case1_2
  IMO2012.A5.case2.A5_case2_real

namespace IMOSL
namespace IMO2012A5

instance : is_empty (ℝ →+* 𝔽₃) :=
  ⟨λ φ, begin
    have h0 := congr_arg φ (mul_inv_cancel (three_ne_zero : (3 : ℝ) ≠ 0)),
    rw [φ.map_mul, φ.map_bit1, φ.map_one] at h0,
    exact (one_ne_zero : (1 : 𝔽₃) ≠ 0) (h0.symm.trans (zero_mul _))
  end⟩

theorem final_solution_real {S : Type*} [comm_ring S] [is_domain S] {f : ℝ → S} :
  good f ↔ (f = λ _, 0) ∨ (∃ φ : ℝ →+* S, f = λ x, φ x - 1) ∨ (∃ φ : ℝ →+* S, f = λ x, φ x ^ 2 - 1) :=
  ⟨λ h, (ne_or_eq (f 0) (-1)).elim
    (λ h0, or.inl $ eq_zero_of_map_zero_ne_neg_one h h0)
    (λ h0, or.inr $ (ne_or_eq (f $ -1) 0).elim
      (λ h1, or.inl $ (eq_or_ne (f $ -1) $ -2).elim
        (case1_1_sol h h0 h1)
        (λ h2, false.rec _ $ is_empty.exists_iff.mp $ case1_2_sol h h0 h1 h2))
      (λ h1, or.inr $ case2_sol h h0 h1)),
  λ h, begin
    rcases h with rfl | ⟨φ, rfl⟩ | ⟨φ, rfl⟩,
    exacts [zero_is_good, good_map_comp_hom case1_1_answer φ,
      good_map_comp_hom case2_answer φ]
  end⟩

end IMO2012A5
end IMOSL
