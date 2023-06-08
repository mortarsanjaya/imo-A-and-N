import IMO2017.A2.A2_basic

/-! # IMO 2017 A2, Case `k = 0` -/

namespace IMOSL
namespace IMO2017A2

variables {R : Type*} [ring R] [decidable_eq R]

lemma good_any_empty (q : R) : good q ∅ :=
  λ u v h _, absurd h not_false

/-- Final solution, `k = 0` -/
theorem final_solution_k_eq_0 (q : R) : excellent 0 q :=
  λ T h, by rw [finset.card_eq_zero.mp h, finset.sub_empty];
    exact good_any_empty q

end IMO2017A2
end IMOSL
