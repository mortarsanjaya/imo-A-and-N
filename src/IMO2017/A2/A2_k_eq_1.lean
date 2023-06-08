import IMO2017.A2.A2_basic

/-! # IMO 2017 A2, Case `k = 1` -/

namespace IMOSL
namespace IMO2017A2

open finset
open_locale pointwise

lemma self_diff_singleton {G : Type*} [add_group G] [decidable_eq G]
  {T : finset G} (h : T.card = 1) : T - T = {0} :=
  exists.elim (card_eq_one.mp h) $ λ a h0, by rw [h0, singleton_sub_singleton, sub_self]

/-- Final solution, `k = 1` -/
theorem final_solution_k_eq_1 {R : Type*} [ring R] [decidable_eq R]
  (q : R) : excellent 1 q :=
  λ T h u v h0 h1,
begin
  rw self_diff_singleton h at h0 h1 ⊢,
  rw [mem_singleton.mp h0, zero_mul, mul_zero],
  exact zero_is_sq_add_diff_of_mem (mem_singleton_self 0)
end

end IMO2017A2
end IMOSL
