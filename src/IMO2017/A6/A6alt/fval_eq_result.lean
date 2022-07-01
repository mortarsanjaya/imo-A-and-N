import
  IMO2017.A6.A6alt.basic
  IMO2017.A6.A6alt.extra.my_poly_induction
  IMO2017.A6.A6alt.extra.zmod2_elts
  data.zmod.algebra
  field_theory.ratfunc

/-!
## Some result implied from f(a) = f(b) for some a, b ∈ F.

We prove that, given a, b ∈ F with f(a) = f(b), we have
1. ∀ P ∈ 𝔽₂[X], f(P(a)) = f(P(b)),
2. ∀ P ∈ 𝔽₂[X], P(a) = 0 ↔ P(b) = 0,
3. ∀ P = Q/R ∈ 𝔽₂(X), R(a), R(b) ≠ 0 → f(P(a)) = f(P(b)).
See "extra/my_poly_induction.lean" for details on induction used for result 1 and 3.
Note that result 2 is trivial from result 1 and f(x) = 0 ↔ x = 0.
-/

open char_two polynomial ratfunc
open_locale polynomial classical

namespace IMOSL
namespace IMO2017A6alt

variables {F : Type*} [field F]



namespace case_char_eq_2

variable [char_p F 2]

def phi2F := algebra_map (zmod 2) F

variables {f : F → F} (feq1 : fn_eq1 f) (feq2 : fn_eq2 f)
variables {a b : F} (fval_eq : f a = f b)
include feq1 feq2 fval_eq



/-- Induction uses "my_poly_induction" in file "extra/my_poly_induction.lean". -/
theorem fF2poly_eq_of_fval_eq (P : (zmod 2)[X]) : f (eval₂ phi2F a P) = f (eval₂ phi2F b P) :=
begin
  revert P; apply extra.my_poly_induction,

  -- ∀ c : R, M(cX)
  { intros c; rcases extra.zmod2_elts c with rfl | rfl,
    rw [map_zero, zero_mul, eval₂_zero, eval₂_zero],
    rw [map_one, one_mul, eval₂_X, eval₂_X, fval_eq] },

  -- ∀ (P : R[X]) (c : R), M(P) → M(P + c)
  { intros P c h; rcases extra.zmod2_elts c with rfl | rfl,
    rw [map_zero, add_zero, h],
    rw [map_one, eval₂_add, eval₂_one, eval₂_add, eval₂_one, feq2, feq2, h] },

  -- ∀ P : R[X], M(P) → M(P + X) → M(P * X)
  { intros P h0 h1,
    rw [eval₂_add, eval₂_X, eval₂_add, eval₂_X] at h1,
    replace h0 := base.lem10 feq1 feq2 h0 fval_eq,
    rw [h1, add_left_inj] at h0,
    rw [eval₂_mul, eval₂_X, eval₂_mul, eval₂_X, h0] }
end

theorem fF2poly_zeroes_eq_of_fval_eq (P : (zmod 2)[X]) : eval₂ phi2F a P = 0 ↔ eval₂ phi2F b P = 0 :=
  by rw [← base.lem3 feq1 feq2, fF2poly_eq_of_fval_eq feq1 feq2 fval_eq, base.lem3 feq1 feq2]

/-- Induction uses "my_poly_induction2" in file "extra/my_poly_induction.lean". -/
theorem fF2ratfunc_eq_of_fval_eq' (P Q : (zmod 2)[X]) :
  f (eval₂ phi2F a P / eval₂ phi2F a Q) = f (eval₂ phi2F b P / eval₂ phi2F b Q) :=
begin
  revert P Q; apply extra.my_poly_induction2,

  -- ∀ (c : F) (P : F[X]), M(P, c)
  { intros c P,
    rcases extra.zmod2_elts c with rfl | rfl,
    rw [map_zero, eval₂_zero, eval₂_zero, div_zero, div_zero],
    rw [map_one, eval₂_one, eval₂_one, div_one, div_one],
    exact fF2poly_eq_of_fval_eq feq1 feq2 fval_eq P },
  
  -- ∀ P Q : F[X], M(P, Q) → M(Q, P)
  { intros P Q h,
    rw [← inv_div, base.lem6 feq1 feq2, h, ← base.lem6 feq1 feq2, inv_div] },

  -- ∀ P Q R : F[X], deg(R) < deg(Q) → M(R, Q) → M(PR, Q) → M(PQ + R, Q)
  { rintros P Q R - h h0,
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
      have h3 := base.lem10 feq1 feq2 (fF2poly_eq_of_fval_eq feq1 feq2 fval_eq P) h,
      rwa [h0, add_right_inj] at h3 } }
end

theorem fF2ratfunc_eq_of_fval_eq (P : ratfunc (zmod 2)) : f (eval phi2F a P) = f (eval phi2F b P) :=
begin
  apply ratfunc.induction_on P; rintros P Q -,
  exact fF2ratfunc_eq_of_fval_eq' feq1 feq2 fval_eq _ _
end



end case_char_eq_2







end IMO2017A6alt
end IMOSL
