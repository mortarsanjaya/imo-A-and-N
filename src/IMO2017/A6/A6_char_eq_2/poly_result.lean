import
  IMO2017.A6.A6_char_eq_2.basic
  data.zmod.basic
  data.polynomial.eval
  data.polynomial.div

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
-/



namespace IMO2017A6

universe u
variable {F : Type u}
variable [field F]



namespace case_char_eq_2

open char_two

variable [char_p F 2]







namespace poly_result

open polynomial

def phi2F := zmod.cast_hom (dvd_refl 2)



variable {f : F → F}
variable feq1 : fn_eq1 f
variable feq2 : fn_eq2 f
include feq1 feq2



lemma fn_induction_intro {a b : F} (h : f a = f b) :
  ∀ P : polynomial (zmod 2),
    f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P) →
      f (eval₂ (phi2F F) a (X + P)) = f (eval₂ (phi2F F) b (X + P)) →
        f (eval₂ (phi2F F) a (X * P)) = f (eval₂ (phi2F F) b (X * P)) :=
begin
  intros P h0 h1,
  rw [eval₂_add, eval₂_X, eval₂_add, eval₂_X] at h1,
  rw [eval₂_mul, eval₂_X, eval₂_mul, eval₂_X],
  let Pa := eval₂ (phi2F F) a P,
  let Pb := eval₂ (phi2F F) b P,
  calc f (a * Pa) = f (a * Pa) + f (a + Pa) - f (a + Pa) : by rw add_sub_cancel
  ... = f (b * Pb) + f (b + Pb) - f (a + Pa) : by rw base_lemma.fn_lem2_7 feq1 feq2 h h0
  ... = f (b * Pb) : by rw [h1, add_sub_cancel],
end

theorem fn_thm {a b : F} (h : f a = f b) :
  ∀ P : polynomial (zmod 2), f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P) :=
begin

  ---- Start with describing all the elements of zmod 2
  have zmod2_elts : ∀ c : zmod 2, c = 0 ∨ c = 1 :=
  begin
    intros c,
    cases c with x x_prop,
    rcases x with _ | x | x,
    left; refl,
    right; refl,
    rw [nat.succ_lt_succ_iff, nat.add_def, add_zero, nat.succ_lt_succ_iff] at x_prop,
    exfalso; exact nat.not_lt_zero x x_prop,
  end,

  ---- Some stupid result
  have zmod2_coe : ∀ c : zmod 2, (phi2F F) c = ↑c :=
  begin
    intros c; cases c,
    unfold phi2F; rw zmod.cast_hom_apply,
  end,

  ---- Another stupid result
  have fn_aux : ∀ (x : F) (c : zmod 2), f (x + c) = f x + c :=
  begin
    intros x c,
    cases zmod2_elts c with h h,
    rw [h, zmod.cast_zero, add_zero, add_zero],
    rw [h, zmod.cast_one', feq2],
  end,

  ---- Start of the main result
  intros P,
  induction h0 : P.nat_degree using nat.strong_induction_on with n n_ih generalizing P,
  cases le_or_lt n 1 with h1 h1,

  -- Case n ≤ 1
  { rw ← h0 at h1,
    rw eq_X_add_C_of_nat_degree_le_one h1,
    simp only [polynomial.eval₂_C, polynomial.eval₂_X, polynomial.eval₂_add, polynomial.eval₂_mul],
    rw [zmod2_coe, zmod2_coe, fn_aux, fn_aux, add_left_inj],
    cases zmod2_elts (P.coeff 1) with Px Px; rw Px; simp,
    exact h, },

  -- Case 1 < n
  { rw [← mod_by_monic_add_div P monic_X, mod_by_monic_X, add_comm, eval₂_add,
        eval₂_add, eval₂_C, eval₂_C, zmod2_coe, fn_aux, fn_aux, add_left_inj],
    suffices : (P /ₘ X).nat_degree < n,
    { apply fn_induction_intro feq1 feq2 h,
      { apply n_ih (P /ₘ X).nat_degree this; refl, },
      { apply n_ih (X + P /ₘ X).nat_degree,
        swap,
        refl,
        apply lt_of_le_of_lt (nat_degree_add_le X _),
        simp only [nat_degree_X, max_lt_iff],
        split; assumption, }, },
    rw [nat_degree_div_by_monic P monic_X, nat_degree_X, h0],
    exact nat.sub_lt (lt_trans zero_lt_one h1) zero_lt_one, },
end

end poly_result







end case_char_eq_2

end IMO2017A6
