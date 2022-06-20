import
  IMO2017.A6.A6_char_eq_2.basic
  IMO2017.A6.A6_char_eq_2.extra.my_poly_induction
  IMO2017.A6.A6_char_eq_2.extra.zmod2_elts
  data.zmod.algebra
  field_theory.ratfunc

namespace IMO2017A6

universe u
variable {F : Type u}
variable [field F]

/-
  Some result implied from f(a) = f(b) for some a, b ∈ F.
  We prove that, given a, b ∈ F with f(a) = f(b), we have
  1. ∀ P ∈ 𝔽₂[X], f(P(a)) = f(P(b)),
  2. ∀ P ∈ 𝔽₂[X], P(a) = 0 ↔ P(b) = 0,
  3. ∀ P = Q/R ∈ 𝔽₂(X), R(a), R(b) ≠ 0 → f(P(a)) = f(P(b))
  See "extra/my_poly_induction.lean" for details on induction needed for result 1 and 3.
-/







open char_two
open polynomial
open ratfunc
open_locale classical

namespace case_char_eq_2



variable [char_p F 2]

def phi2F := algebra_map (zmod 2) F

variables {f : F → F} (feq1 : fn_eq1 f) (feq2 : fn_eq2 f)
variables {a b : F} (fval_eq : f a = f b)
include feq1 feq2 fval_eq



/-
  Proof of result 1 (∀ P ∈ 𝔽₂[X], f(P(a)) = f(P(b))):
  Refer to theorem "my_poly_induction" in file "extra/my_poly_induction.lean".
-/
theorem fF2poly_eq_of_fval_eq (P : polynomial (zmod 2)) :
  f (eval₂ phi2F a P) = f (eval₂ phi2F b P) :=
begin
  revert P; apply extra.my_poly_induction,

  -- ∀ c : R, M(cX)
  { intros c,
    cases extra.zmod2_elts c with h h,
    rw [h, map_zero, zero_mul, eval₂_zero, eval₂_zero],
    rw [h, map_one, one_mul, eval₂_X, eval₂_X, fval_eq] },

  -- ∀ (P : R[X]) (c : R), M(P) → M(P + c)
  { intros P c h,
    cases extra.zmod2_elts c with h0 h0,
    rw [h0, map_zero, add_zero, h],
    rw [h0, map_one, eval₂_add, eval₂_one, eval₂_add, eval₂_one, feq2, feq2, h] },

  -- ∀ P : R[X], M(P) → M(P + X) → M(P * X)
  { intros P h0 h1,
    rw [eval₂_add, eval₂_X, eval₂_add, eval₂_X] at h1,
    rw [eval₂_mul, eval₂_X, eval₂_mul, eval₂_X],
    let Pa : F := eval₂ phi2F a P,
    let Pb : F := eval₂ phi2F b P,
    calc f (Pa * a) = f (Pa * a) + f (Pa + a) - f (Pa + a) : by rw add_sub_cancel
    ... = f (Pb * b) + f (Pb + b) - f (Pa + a) : by rw base_lemma.fn_lem2_7 feq1 feq2 h0 fval_eq
    ... = f (Pb * b) + f (Pb + b) - f (Pb + b) : by rw h1
    ... = f (Pb * b) : by rw add_sub_cancel },
end



/-
  Proof of result 2 (∀ P ∈ 𝔽₂[X], P(a) = 0 ↔ P(b) = 0):
  Trivial from result 1 and f(x) = 0 ↔ x = 0
-/
theorem fF2poly_zeroes_eq_of_fval_eq (P : polynomial (zmod 2)) :
  eval₂ phi2F a P = 0 ↔ eval₂ phi2F b P = 0 :=
begin
  rw [← base_lemma.fn_lem1_3 feq1 feq2,
      fF2poly_eq_of_fval_eq feq1 feq2 fval_eq,
      base_lemma.fn_lem1_3 feq1 feq2],
end



/-
  Proof of result 3 (∀ P = Q/R ∈ 𝔽₂(X), R(a), R(b) ≠ 0 → f(P(a)) = f(P(b))):
  Refer to theorem "my_poly_induction2" in file "extra/my_poly_induction.lean".
  We start by stating the result in terms of just polynomials.
  Afterwards, we state the result in terms of rational functions.
-/
theorem fF2ratfunc_eq_of_fval_eq' (P Q : polynomial (zmod 2)) :
  f (eval₂ phi2F a P / eval₂ phi2F a Q) = f (eval₂ phi2F b P / eval₂ phi2F b Q) :=
begin
  revert P Q; apply extra.my_poly_induction2,

  -- ∀ (c : F) (P : F[X]), M(P, c)
  { intros c P,
    cases extra.zmod2_elts c with h h,
    rw [h, map_zero, eval₂_zero, eval₂_zero, div_zero, div_zero],
    rw [h, map_one, eval₂_one, eval₂_one, div_one, div_one],
    exact fF2poly_eq_of_fval_eq feq1 feq2 fval_eq P },
  
  -- ∀ P Q : F[X], M(P, Q) → M(Q, P)
  { intros P Q h,
    rw [← inv_div, base_lemma.fn_lem2_3 feq1 feq2, h,
        ← base_lemma.fn_lem2_3 feq1 feq2, inv_div] },

  -- ∀ P Q R : F[X], deg(R) < deg(Q) → M(R, Q) → M(PR, Q) → M(PQ + R, Q)
  { intros P Q R junk h h0,
    by_cases h1 : eval₂ phi2F a Q = 0,

    -- Case 1: Q(a) = 0
    { rw [h1, div_zero],
      rw fF2poly_zeroes_eq_of_fval_eq feq1 feq2 fval_eq at h1,
      rw [h1, div_zero] },

    -- Case 2: Q(a) ≠ 0
    { rw [eval₂_mul, ← mul_div, eval₂_mul, ← mul_div] at h0,
      rw [eval₂_add, eval₂_mul, ← add_div_eq_mul_add_div _ _ h1],
      rw fF2poly_zeroes_eq_of_fval_eq feq1 feq2 fval_eq at h1,
      rw [eval₂_add, eval₂_mul, ← add_div_eq_mul_add_div _ _ h1],
      have h2 := fF2poly_eq_of_fval_eq feq1 feq2 fval_eq P,
      let Pa : F := eval₂ phi2F a P,
      let Pb : F := eval₂ phi2F b P,
      let RQa : F := eval₂ phi2F a R / eval₂ phi2F a Q,
      let RQb : F := eval₂ phi2F b R / eval₂ phi2F b Q,
      calc f (Pa + RQa) = f (Pa * RQa) + f (Pa + RQa) - f (Pa * RQa) : by rw add_sub_cancel'
      ... = f (Pb * RQb) + f (Pb + RQb) - f (Pa * RQa) : by rw base_lemma.fn_lem2_7 feq1 feq2 h2 h
      ... = f (Pb * RQb) + f (Pb + RQb) - f (Pb * RQb) : by rw h0
      ... = f (Pb + RQb) : by rw add_sub_cancel' } },
end

theorem fF2ratfunc_eq_of_fval_eq (P : ratfunc (zmod 2)) :
  f (eval phi2F a P) = f (eval phi2F b P) :=
begin
  apply ratfunc.induction_on P; intros,
  apply fF2ratfunc_eq_of_fval_eq' feq1 feq2 fval_eq,
end



end case_char_eq_2







end IMO2017A6
