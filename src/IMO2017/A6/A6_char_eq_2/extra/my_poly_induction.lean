import data.polynomial.field_division

/-!
# Induction on Polynomials  
  
Implementation of induction necessary for results given in "fval_eq_result.lean"
-/

open polynomial
open_locale polynomial classical

namespace IMOSL
namespace IMO2017A6
namespace extra

/-- An auxiliary lemma of nat_degree of a modulo -/
theorem polynomial.nat_degree_mod_lt {F : Type*} [field F]
    (P : F[X]) {Q : F[X]} (hQ : 0 < Q.nat_degree) :
  (P % Q).nat_degree < Q.nat_degree :=
begin
  rcases eq_or_ne (P % Q) 0 with h | h,
  rwa [h, nat_degree_zero],
  have h0 := ne_zero_of_nat_degree_gt hQ,
  rw [nat_degree_lt_nat_degree_iff h, mod_def],
  refine lt_of_lt_of_eq (degree_mod_by_monic_lt _ _) (degree_mul_C _),
  exacts [monic_mul_leading_coeff_inv h0, (inv_ne_zero (leading_coeff_ne_zero.mpr h0))]
end

/-- An auxiliary lemma of nat_degree of a div -/
theorem polynomial.nat_degree_add_div {F : Type*} [field F]
    {P Q : F[X]} (hQ0 : Q ≠ 0) (hPQ : Q.nat_degree ≤ P.nat_degree) :
  Q.nat_degree + (P / Q).nat_degree = P.nat_degree :=
begin
  have h : (Q.leading_coeff)⁻¹ ≠ 0 := inv_ne_zero (leading_coeff_ne_zero.mpr hQ0),
  rw [div_def, nat_degree_C_mul h, nat_degree_div_by_monic,
      nat_degree_mul_C h, add_comm, nat.sub_add_cancel hPQ],
  exact (monic_mul_leading_coeff_inv hQ0)
end



/-- Strong induction on degree of polynomial, using nat_degree (with deg(0) = 0). -/
theorem polynomial_strong_induction_nat_degree {R : Type*} [comm_ring R] {M : R[X] → Prop}
  (h : ∀ P : R[X], (∀ Q : R[X], Q.nat_degree < P.nat_degree → M Q) → M P) :
  ∀ P : R[X], M P :=
begin
  intros P; induction h0 : P.nat_degree using nat.strong_induction_on with n n_ih generalizing P,
  simp only [] at n_ih,
  apply h; intros Q h1,
  rw h0 at h1,
  exact n_ih Q.nat_degree h1 Q rfl
end

/--
  Let R be a non-trivial commutative ring and take some M : R[X] → Prop.
  Then, M(P) holds for all P ∈ R[X] if all the following are true:
  (1). For any c ∈ R, M(cX) holds,
  (2). For any P ∈ R[X] and c ∈ R, M(P) → M(P + c),
  (3). For any P ∈ R[X], M(P) → M(P + X) → M(P * X).

  Proof:
    By strong induction on deg(P).

    Base case (deg(P) ≤ 1):
      For deg(P) ≤ 1, P = cX + d for c, d ∈ R[X].
      By (1), M(cX) holds, and then by (2), M(P) holds.

    Induction step (deg(P) > 1):
      Suppose that for some n > 1, we have M(P) for all P ∈ R[X] with deg(P) < n.
      Take some P with deg(P) = n.
      By (2), we can WLOG assume X | P.

      Now, write P = QX for some Q ∈ R[X].
      Since deg(Q) < deg(P) = n, by IH, we have M(Q).
      But also, M(Q + X) holds since deg(Q + X) ≤ max {deg(Q), 1} < n.
      Thus, by (3), we have M(P).
-/
theorem my_poly_induction {R : Type*} [nontrivial R] [comm_ring R] {M : R[X] → Prop}
  (M_base : ∀ c : R, M (C c * X)) (M_ih1 : ∀ (P : R[X]) (d : R), M P → M (P + C d))
  (M_ih2 : ∀ P : R[X], M P → M (P + X) → M (P * X)) (P : R[X]) : M P :=
begin
  apply polynomial_strong_induction_nat_degree; intros P P_ih,
  cases le_or_lt P.nat_degree 1 with h h,
  rw eq_X_add_C_of_nat_degree_le_one h,
  exact M_ih1 _ _ (M_base (P.coeff 1)),
  rw [← mod_by_monic_add_div P monic_X, mod_by_monic_X, add_comm, mul_comm],
  have h1 : (P /ₘ X).nat_degree < P.nat_degree :=
    by rw [nat_degree_div_by_monic P monic_X, nat_degree_X];
      exact nat.sub_lt (lt_trans zero_lt_one h) zero_lt_one,
  refine M_ih1 _ _ (M_ih2 _ (P_ih _ h1) (P_ih _ (lt_of_le_of_lt (nat_degree_add_le _ X) _))),
  rw nat_degree_X; exact max_lt h1 h
end

/--
  Let F be a field and take some M : F[X] × F[X] → Prop.
  Then, M(P, Q) holds for all P, Q ∈ F[X] if all the following are true:
  (1). For all c ∈ F and P ∈ F[X], M(P, c) holds,
  (2). For all P Q ∈ F[X], M(P, Q) → M(Q, P),
  (3). For all P Q R ∈ F[X] with deg(R) < deg(Q), M(R, Q) → M(PR, Q) → M(PQ + R, Q).

  Proof:
    By strong induction on deg(Q), and then strong induction on deg(P).
    
    Base case (deg(Q) = 0):
      This is essentially (1) since deg(Q) ≤ 0 forces Q to be constant.

    Induction step (deg(Q) > 0):
      Suppose that M(P, Q₁) holds for all P and Q₁ with deg(Q₁) < deg(Q).
      We now use strong induction on deg(P).

      Base case (deg(P) < deg(Q)):
        We have M(Q, P) by IH and then M(P, Q) by (2).
      
      Induction step (deg(P) ≥ deg(Q)):
        Suppose that M(P₁, Q) holds for all P₁ with deg(P₁) < deg(P).
        Using division algorithm, we can write P = P₀ Q + R with deg(R) < deg(Q).
        Since deg(Q) ≤ deg(P), we have M(R, Q) by IH.
        Next, deg(P) = deg(P₀ Q) > deg(P₀ R), so IH gives us M(P₀ R, Q).
        Then (3) gives us M(P₀ Q + R, Q) = M(P, Q), as desired.

  Implementation details:
  • In the induction step, the case Q | P and Q ∤ P require different proof steps.
    Thus, we will separate these two cases.
-/
theorem my_poly_induction2 {F : Type*} [field F] {M : F[X] → F[X] → Prop}
  (M_base : ∀ (c : F) (P : F[X]), M P (C c)) (M_ih1 : ∀ P Q : F[X], M P Q → M Q P)
  (M_ih2 : ∀ P Q R : F[X], R.nat_degree < Q.nat_degree → M R Q → M (P * R) Q → M (P * Q + R) Q)
  (P Q : F[X]) : M P Q :=
begin
  revert Q P; refine polynomial_strong_induction_nat_degree _; intros Q Q_ih,
  cases nat.eq_zero_or_pos Q.nat_degree with h h,
  rw eq_C_of_nat_degree_eq_zero h,
  exact M_base (Q.coeff 0),
  refine polynomial_strong_induction_nat_degree _; intros P P_ih,
  cases lt_or_le P.nat_degree Q.nat_degree with h0 h0,
  exact M_ih1 _ _ (Q_ih P h0 Q),
  ---- The main induction step
  rw [← euclidean_domain.mod_add_div P Q, add_comm, mul_comm],
  have h1 := polynomial.nat_degree_mod_lt P h,
  refine M_ih2 _ _ _ h1 (P_ih (P % Q) (lt_of_lt_of_le h1 h0)) (P_ih _ _),
  clear M_base M_ih1 M_ih2 P_ih Q_ih M,
  cases eq_or_ne (P % Q) 0 with h2 h2,
  rw [h2, mul_zero, nat_degree_zero],
  exact lt_of_lt_of_le h h0,
  cases eq_or_ne (P / Q) 0 with h3 h3,
  rw [h3, zero_mul, nat_degree_zero],
  exact lt_of_lt_of_le h h0,
  rw [nat_degree_mul h3 h2, ← polynomial.nat_degree_add_div _ h0, add_comm, add_lt_add_iff_right],
  exacts [polynomial.nat_degree_mod_lt P h, ne_zero_of_nat_degree_gt h]
end

end extra
end IMO2017A6
end IMOSL
