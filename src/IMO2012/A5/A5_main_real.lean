import
  IMO2012.A5.cases.A5_case1_1
  IMO2012.A5.cases.A5_case1_2
  IMO2012.A5.cases.A5_case2_real

namespace IMOSL
namespace IMO2012A5

theorem final_solution_real {S : Type*} [comm_ring S] [is_domain S] {f : ℝ → S} :
  good f ↔ (f = λ _, 0) ∨ (∃ φ : ℝ →+* S, f = λ x, φ x - 1) ∨ (∃ φ : ℝ →+* S, f = λ x, φ x ^ 2 - 1) :=
  ⟨λ h, (ne_or_eq (f 0) (-1)).elim
    (λ h0, or.inl $ eq_zero_of_map_zero_ne_neg_one h h0)
    (λ h0, or.inr $ (ne_or_eq (f $ -1) 0).elim
      (λ h1, or.inl $ (eq_or_ne (f $ -1) $ -2).elim
        (case1_1_sol h h0 h1)
        (λ h2, absurd h2 $ case1_2_real_sol h h0 h1))
      (λ h1, or.inr $ case2_sol h h0 h1)),
  λ h, begin
    rcases h with rfl | ⟨φ, rfl⟩ | ⟨φ, rfl⟩,
    exacts [zero_is_good, good_map_comp_hom case1_1_answer φ,
      good_map_comp_hom case2_answer φ]
  end⟩

end IMO2012A5
end IMOSL
