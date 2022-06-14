import
  data.polynomial.basic
  data.polynomial.degree.lemmas

namespace IMO2017A6
namespace extra

open polynomial
open_locale classical

universe u



/-
  This file contains the proof of the following result.
  For any c ∈ F ∖ {0} and P ∈ F[X], deg(cP) = deg(P).
  Note: the degree used is nat_degree.
-/
theorem nat_degree_C_mul_eq_of_C_ne_zero {F : Type u} [field F] {c : F} (h : c ≠ 0) :
  ∀ P : polynomial F, (C c * P).nat_degree = P.nat_degree :=
begin
  intros P,
  by_cases h0 : P = 0,
  rw [h0, mul_zero],
  apply nat_degree_C_mul_eq_of_mul_ne_zero,
  apply mul_ne_zero h,
  rw leading_coeff_ne_zero; exact h0,
end



end extra
end IMO2017A6
