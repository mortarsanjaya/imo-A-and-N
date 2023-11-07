import IMO2017.A2.A2_basic

/-! # IMO 2017 A2, Case `k = 1` -/

namespace IMOSL
namespace IMO2017A2

open finset
open_locale pointwise

lemma self_diff_singleton {G : Type*} [add_group G] [decidable_eq G]
  {T : finset G} (h : T.card = 1) : T - T = 0 :=
  exists.elim (card_eq_one.mp h) $ λ a h0, (congr_arg2 has_sub.sub h0 h0).trans $
    (singleton_sub_singleton a a).trans $ congr_arg _ (sub_self a)
  
variables {R : Type*} [ring R]

lemma good_any_singleton_zero (q : R) : good q 0 :=
  λ u v h1 h0, (mem_singleton.mp h0).symm ▸ (mul_zero u).symm ▸ (mul_zero q).symm ▸
    zero_is_sq_add_diff_of_mem (mem_singleton_self 0)

/-- Final solution, `k = 1` -/
theorem final_solution_k_eq_1 {R : Type*} [ring R] [decidable_eq R] (q : R) : excellent 1 q :=
  λ T h, (self_diff_singleton h).symm ▸ good_any_singleton_zero q

end IMO2017A2
end IMOSL
