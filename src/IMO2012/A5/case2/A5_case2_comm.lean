import algebra.ring.commute

/-! # IMO 2012 A5, Commutativity Lemmas for Case 2: `f(-1) = 0` -/

namespace IMOSL
namespace IMO2012A5

variables {R : Type*} [ring R]

lemma comm_self_add_one (x : R) : commute x (x + 1) :=
  (commute.refl x).add_right $ commute.one_right x

lemma comm_self_sub_one (x : R) : commute x (x - 1) :=
  (commute.refl x).sub_right $ commute.one_right x

lemma comm_add_one_sub_one (x : R) : commute (x + 1) (x - 1) :=
  (comm_self_sub_one x).add_left $ commute.one_left (x - 1)

end IMO2012A5
end IMOSL
