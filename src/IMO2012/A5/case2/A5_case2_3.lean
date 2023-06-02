import IMO2012.A5.case2.A5_case2_general algebra.group_power.ring

/-! # IMO 2012 A5, Case 2.3: `f(2) = 3 ≠ 1` -/

namespace IMOSL
namespace IMO2012A5

section answer

variables {R : Type*} [comm_ring R]

private lemma sq_sub_one (x : R) : x ^ 2 - 1 = (x + 1) * (x - 1) :=
  by rw [← sq_sub_sq, one_pow]

/-- The respective solution for the subcase. -/
theorem case2_3_answer {R : Type*} [comm_ring R] : good (λ x : R, x ^ 2 - 1) :=
  λ x y, (sub_sub_sub_cancel_right _ _ _).trans $ (sq_sub_sq _ _).trans $ eq.symm $
    (congr_arg2 has_mul.mul (sq_sub_one x) (sq_sub_one y)).trans $
    (mul_mul_mul_comm _ _ _ _).trans $ congr_arg2 has_mul.mul
      (by rw [add_one_mul, mul_add_one, add_comm y 1, add_add_add_comm])
      (by rw [sub_one_mul, mul_sub_one, sub_sub,
        ← add_sub_assoc, ← sub_add, ← add_sub_right_comm])

end answer



section noncomm_ring

variables {R S : Type*} [ring R] [ring S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 3)
include h h0 h1

/- Needs to be filled in -/

end noncomm_ring

end IMO2012A5
end IMOSL
