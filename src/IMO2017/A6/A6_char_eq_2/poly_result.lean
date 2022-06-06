import
  IMO2017.A6.A6_char_eq_2.base_lemma
  data.zmod.basic
  data.zmod.algebra
  data.polynomial.basic
  data.polynomial.eval

/-
  Results involving the polynomial ring 𝔽₂[t]
-/



namespace IMO2017A6

universe u
variable F : Type u
variable [field F]



namespace case_char_eq_2

open char_two

variable [char_p F 2]







namespace poly_result

def phi2F := (zmod.algebra F 2).to_ring_hom

variable f : F → F
variable feq1 : fn_eq1 F f
variable feq2 : fn_eq2 F f
include feq1 feq2



theorem fn_thm1 (a b : F) (h : f a = f b) :
  ∀ P : polynomial (zmod 2),
    f (polynomial.eval₂ (phi2F F) a P) = f (polynomial.eval₂ (phi2F F) b P) :=
-- We prove by induction on degree of P
begin
  -- Statement setup for induction
  let M := λ n : ℕ, (∀ P : polynomial (zmod 2),
    P.nat_degree ≤ n → f (polynomial.eval₂ (phi2F F) a P) = f (polynomial.eval₂ (phi2F F) b P)),
  suffices : ∀ n : ℕ, M n,
  { intros P,
    apply this P.nat_degree,
    exact le_refl P.nat_degree, },
  intros n,
  induction n,
  { intros P,
    sorry, },
  sorry,
end







end poly_result






end case_char_eq_2

end IMO2017A6
