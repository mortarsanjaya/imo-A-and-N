import IMO2012.A5.case2.A5_case2_lemmas

/-! # IMO 2012 A5, Case 2.3: `f(2) = 3 ≠ 1` -/

namespace IMOSL
namespace IMO2012A5

lemma sq_sub_one_is_good {R : Type*} [comm_ring R] : good (λ x : R, x ^ 2 - 1) :=
  λ x y, by rw [sub_sub_sub_cancel_right, sq_sub_sq]


end IMO2012A5
end IMOSL
