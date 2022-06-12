import
  IMO2017.A6.A6_char_eq_2.basic
  IMO2017.A6.A6_char_eq_2.extra.my_poly_induction
  IMO2017.A6.A6_char_eq_2.extra.zmod2_elts
  data.zmod.algebra

namespace IMO2017A6

universe u
variable {F : Type u}
variable [field F]

/-
  We prove that, given a, b ∈ F with f(a) = f(b), we have
  1. ∀ P ∈ 𝔽₂[X], f(P(a)) = f(P(b)),
  2. ∀ P ∈ 𝔽₂[X], P(a) = 0 ↔ P(b) = 0,
  3. ∀ P = Q/R ∈ 𝔽₂(X), R(a), R(b) ≠ 0 → f(P(a)) = f(P(b))
  See "extra/my_F2X_induction.lean" for details on induction needed for result 1 and 3.

  TODO: State and prove result 3.
-/

namespace case_char_eq_2

open char_two
open polynomial
open ratfunc

variable [char_p F 2]

def phi2F := algebra_map (zmod 2) F

variable {f : F → F}
variable feq1 : fn_eq1 f
variable feq2 : fn_eq2 f
variable {a : F}
variable {b : F}
variable fval_eq : f a = f b
include feq1 feq2 fval_eq







/-
  Proof of result 1 (∀ P ∈ 𝔽₂[X], f(P(a)) = f(P(b))):
  Strong induction on deg(P) with deg(P) ≤ 1 as a base case.
  Note that:
  1. For any c ∈ 𝔽₂, the equation is true for cX.
     Trivial since c = 0 or 1 and the equation is trivially true for 0 and X.
  2. For any c ∈ 𝔽₂, the equation is true for P + c if it is true for P.
     Due to f(x + 1) = f(x) + 1 (FE 2 of the new FE system) and c = 0 or 1.
  3. The equation is true for PX if it is true for P and P + X.
     Due to f(a) = f(b) → f(c) = f(d) → f(ac) + f(a + c) = f(bd) + f(b + d) (base lemma 2.7).
  See "extra/my_F2X_induction.lean", theorem "my_poly_induction".
-/
theorem fF2poly_eq_of_fval_eq :
  ∀ P : polynomial (zmod 2), f (eval₂ phi2F a P) = f (eval₂ phi2F b P) :=
begin
  apply extra.my_poly_induction,
  { intros c,
    cases extra.zmod2_elts c with h h,
    rw [h, map_zero, zero_mul, eval₂_zero, eval₂_zero],
    rw [h, map_one, one_mul, eval₂_X,eval₂_X, fval_eq] },
  { intros P c h,
    cases extra.zmod2_elts c with h0 h0,
    rw [h0, map_zero, add_zero, h],
    rw [h0, map_one, eval₂_add, eval₂_add, eval₂_one, eval₂_one, feq2, feq2, h] },
  { intros P h0 h1,
    rw [eval₂_add, eval₂_X, eval₂_add, eval₂_X] at h1,
    rw [eval₂_mul, eval₂_X, eval₂_mul, eval₂_X],
    let Pa : F := eval₂ phi2F a P,
    let Pb : F := eval₂ phi2F b P,
    calc f (Pa * a) = f (Pa * a) + f (Pa + a) - f (Pa + a) : by rw add_sub_cancel
    ... = f (Pb * b) + f (Pb + b) - f (Pa + a) : by rw base_lemma.fn_lem2_7 feq1 feq2 h0 fval_eq
    ... = f (Pb * b) : by rw [h1, add_sub_cancel] },
end







end case_char_eq_2

end IMO2017A6
