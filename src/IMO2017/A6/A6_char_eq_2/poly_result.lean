import
  IMO2017.A6.A6_char_eq_2.base_lemma
  data.zmod.basic
  data.zmod.algebra
  data.polynomial.basic
  data.polynomial.eval

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
-/

namespace case_char_eq_2

open char_two

variable [char_p F 2]







namespace poly_result

open polynomial

def phi2F := (zmod.algebra F 2).to_ring_hom

variable f : F → F
variable feq1 : fn_eq1 F f
variable feq2 : fn_eq2 F f
include feq1 feq2



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
  sorry,
end

theorem fn_thm1 (a b : F) (h : f a = f b) :
  ∀ P : polynomial (zmod 2), f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P) :=
-- We prove by induction on degree of P
begin
  -- Statement setup for induction
  let M := λ n : ℕ, ∀ P : polynomial (zmod 2),
    P.nat_degree ≤ n → f (eval₂ (phi2F F) a P) = f (eval₂ (phi2F F) b P),
  suffices : ∀ n : ℕ, M n,
  { intros P,
    apply this P.nat_degree,
    exact le_refl P.nat_degree, },
  intros n,
  induction n with n,
  { intros P h0,
    rw eq_C_of_nat_degree_le_zero h0,
    simp, },
  { cases n,
    { intros P h0,
      have h1 := exists_eq_X_add_C_of_nat_degree_le_one h0,
      rcases h1 with ⟨⟨a, a_prop⟩, ⟨b, b_prop⟩, h1⟩,
      sorry, },
    { suffices : 1 ≤ n.succ,
      { exact fn_lem2 F f feq1 feq2 a b h n.succ this n_ih, },
      rw nat.succ_le_iff,
      exact nat.succ_pos n, }, },
end







end poly_result






end case_char_eq_2

end IMO2017A6
