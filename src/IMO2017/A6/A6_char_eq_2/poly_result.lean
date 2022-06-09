import
  IMO2017.A6.A6_char_eq_2.base_lemma
  data.zmod.basic
  data.zmod.algebra
  data.polynomial.basic
  data.polynomial.eval
  data.polynomial.inductions

/-
  Results involving the polynomial ring 𝔽₂[X]
-/



namespace IMO2017A6

universe u
variable F : Type u
variable [field F]

/-
  The big polynomial result: for any a, b ∈ F, if f(a) = f(b), then
          ∀ P ∈ 𝔽₂[X], f(P(a)) = f(P(b))
  We proceed by induction on deg(P)
-/

namespace case_char_eq_2

open char_two

variable [char_p F 2]







namespace poly_result

open polynomial

def phi2F := zmod.cast_hom (dvd_refl 2)

lemma zmod2_values :
  ∀ c : zmod 2, c = 0 ∨ c = 1 :=
begin
  intros c,
  cases c with x x_prop,
  rcases x with _ | x | x,
  { left; refl, },
  { right; refl, },
  { exfalso,
    rw [nat.succ_lt_succ_iff, nat.add_def, add_zero, nat.succ_lt_succ_iff] at x_prop,
    have := nat.not_lt_zero x,
    contradiction, },
end

lemma zmod2_coe :
  ∀ c : zmod 2, (phi2F F) c = ↑c :=
begin
  intros c,
  cases c,
  unfold phi2F,
  simp,
end



variable f : F → F
variable feq1 : fn_eq1 F f
variable feq2 : fn_eq2 F f
include feq1 feq2



lemma fn_aux :
  ∀ (x : F) (c : zmod 2), f (x + c) = f x + c :=
begin
  intros x c,
  cases (zmod2_values c) with h h,
  all_goals { subst h; simp, },
  exact feq2 x,
end

lemma fn_lem1 (a b : F) (h : f a = f b) :
  ∀ P : polynomial (zmod 2),
    f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P) →
      f (eval₂ (phi2F F) a (P + X)) = f (eval₂ (phi2F F) b (P + X)) →
        f (eval₂ (phi2F F) a (P * X)) = f (eval₂ (phi2F F) b (P * X)) :=
begin
  simp,
  intros P h0 h1,
  let c := eval₂ (phi2F F) a P,
  let d := eval₂ (phi2F F) b P,
  have h2 := base_lemma.fn_lem2_5 F f feq1 feq2 a b h c,
  have h3 := base_lemma.fn_lem2_5 F f feq1 feq2 c d h0 b,
  rwa [mul_comm c b, add_comm c b, ← h2,
       mul_comm a c, add_comm a c, h1, add_left_inj] at h3,
end

lemma fn_lem2 (a b : F) (h : f a = f b) (n : ℕ) (h0 : 1 ≤ n) :
  (∀ P : polynomial (zmod 2), P.nat_degree ≤ n →
    f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P)) →
  (∀ P : polynomial (zmod 2), P.nat_degree ≤ n.succ →
    f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P)) :=
begin
  intros M_in P h1,
  rw [← div_X_mul_X_add P, eval₂_add, eval₂_add, eval₂_C, eval₂_C,
      zmod2_coe, fn_aux F f feq1 feq2, fn_aux F f feq1 feq2, add_left_inj],
  have h2 : P.div_X.nat_degree ≤ n,
  { rw ← nat.lt_succ_iff,
    sorry, },
  apply fn_lem1 F f feq1 feq2 a b h,
  { apply M_in,
    exact h2, },
  { apply M_in,
    apply nat_degree_add_le_of_degree_le,
    exact h2,
    simp; exact h0, },
end

theorem fn_thm (a b : F) (h : f a = f b) :
  ∀ P : polynomial (zmod 2), f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P) :=
begin
  let M := λ n : ℕ, ∀ P : polynomial (zmod 2),
    P.nat_degree ≤ n → f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P),
  suffices : ∀ n : ℕ, M n,
  { intros P,
    apply this P.nat_degree,
    exact le_refl P.nat_degree, },

  intros n,
  induction n with n,

  ---- Case n = 0
  { intros P h0,
    rw eq_C_of_nat_degree_le_zero h0,
    simp, },
  
  cases n,
  ---- Case n = 1
  { intros P h0,
    rcases exists_eq_X_add_C_of_nat_degree_le_one h0 with ⟨c, d, h1⟩,
    rw h1; simp,
    rw [zmod2_coe, zmod2_coe, fn_aux F f feq1 feq2, fn_aux F f feq1 feq2, add_left_inj],
    cases zmod2_values c with h2 h2; subst h2; simp,
    exact h, },
  
  ---- Case n > 1
  { have h0 := nat.succ_pos n,
    rw [nat.lt_iff_add_one_le, zero_add] at h0,
    exact fn_lem2 F f feq1 feq2 a b h n.succ h0 n_ih, },

end



end poly_result






end case_char_eq_2

end IMO2017A6
