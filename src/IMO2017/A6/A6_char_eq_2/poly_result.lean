import
  IMO2017.A6.A6_char_eq_2.basic
  IMO2017.A6.A6_char_eq_2.extra.my_F2X_induction
  data.zmod.algebra

namespace IMO2017A6

universe u
variable {F : Type u}
variable [field F]

/-
  The big polynomial result: for any a, b ∈ F, if f(a) = f(b), then
          ∀ P ∈ 𝔽₂[X], f(P(a)) = f(P(b))

  Proof:
  Strong induction on deg(P) with deg(P) ≤ 1 as a base case.

  Base case:
  For deg(P) ≤ 1, P = cX + d for c, d ∈ 𝔽₂[X]
  For c = 0, trivial
  For c = 1, d = 0, trivial as well
  For c = 1, d = 1, true by f(x + 1) = f(x) + 1

  Induction step:
  Suppose that for some n > 1, the above result holds whenever deg(P) < n.
  Take some P with deg(P) = n.
  By f(x + 1) = f(x) + 1, WLOG we can assume that X ∣ P.
  Write P = XQ for some Q ∈ 𝔽₂[X].
  Since deg(Q) < deg(P) = n, by IH, f(Q(a)) = f(Q(b)).
  Together with f(a) = f(b), we get f(Q(a) a) + f(Q(a) + a) = f(Q(b) b) + f(Q(b) + b).
  But Q + X has degree ≤ max(1, deg(Q)) < n.
  Thus, f(Q(a) + a) = f(Q(b) + b), which implies f(Q(a) a) = f(Q(b) b).



  Implementation details:
  We will need to rewrite our own induction step for this problem.
  See file "extra/my_F2X_induction.lean".
-/



namespace case_char_eq_2

open char_two

variable [char_p F 2]







namespace poly_result

open polynomial

def phi2F := algebra_map (zmod 2) F



variable {f : F → F}
variable feq1 : fn_eq1 f
variable feq2 : fn_eq2 f
include feq1 feq2



theorem fn_thm {a b : F} (h : f a = f b) :
  ∀ P : polynomial (zmod 2), f (eval₂ phi2F a P) = f (eval₂ phi2F b P) :=
begin
  apply extra.my_F2X_induction.induction1,
  { rw [eval₂_zero, eval₂_zero] },
  { rwa [eval₂_X, eval₂_X] },
  { intros P h,
    rw [eval₂_add, eval₂_one, feq2, h, eval₂_add, eval₂_one, feq2] },
  { intros P h0 h1,
    rw [eval₂_add, eval₂_X, eval₂_add, eval₂_X] at h1,
    rw [eval₂_mul, eval₂_X, eval₂_mul, eval₂_X],
    let Pa : F := eval₂ phi2F a P,
    let Pb : F := eval₂ phi2F b P,
    calc f (Pa * a) = f (Pa * a) + f (Pa + a) - f (Pa + a) : by rw add_sub_cancel
    ... = f (Pb * b) + f (Pb + b) - f (Pa + a) : by rw base_lemma.fn_lem2_7 feq1 feq2 h0 h
    ... = f (Pb * b) : by rw [h1, add_sub_cancel] },
end

end poly_result







end case_char_eq_2

end IMO2017A6
