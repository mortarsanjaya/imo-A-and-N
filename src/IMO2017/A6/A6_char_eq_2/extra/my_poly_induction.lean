import
  data.polynomial.basic
  data.polynomial.field_division

/-
  Implementation of induction necessary for results given in "poly_result.lean"
-/
namespace IMO2017A6
namespace extra

open polynomial
open_locale classical

universe u



/-
  Strong induction on degree of polynomial, using nat_degree (with deg(0) = 0)
-/
theorem polynomial_strong_induction_nat_degree {R : Type u} [comm_ring R] {M : polynomial R → Prop}
  (h : ∀ P : polynomial R, (∀ Q : polynomial R, Q.nat_degree < P.nat_degree → M Q) → M P) :
  ∀ P : polynomial R, M P :=
begin
  intros P,
  induction h0 : P.nat_degree using nat.strong_induction_on with n n_ih generalizing P,
  apply h; intros Q h1,
  rw h0 at h1,
  apply n_ih Q.nat_degree h1,
  refl,
end



/-
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
theorem my_poly_induction {R : Type u} [nontrivial R] [comm_ring R] {M : polynomial R → Prop} :
  (∀ c : R, M (C c * X)) →
  (∀ (P : polynomial R) (d : R), M P → M (P + C d)) →
  (∀ P : polynomial R, M P → M (P + X) → M (P * X)) →
  ∀ P : polynomial R, M P :=
begin
  intros M_base M_ih1 M_ih2,
  apply polynomial_strong_induction_nat_degree; intros P P_ih,
  cases le_or_lt P.nat_degree 1 with h h,

  -- Base case: deg(P) ≤ 1
  { rw eq_X_add_C_of_nat_degree_le_one h,
    apply M_ih1,
    exact M_base (P.coeff 1) },
  
  -- Induction step: deg(P) > 1
  { rw [← mod_by_monic_add_div P monic_X, mod_by_monic_X, add_comm, mul_comm],
    apply M_ih1,
    have h1 : (P /ₘ X).nat_degree < P.nat_degree,
    { rw [nat_degree_div_by_monic P monic_X, nat_degree_X],
      exact nat.sub_lt (lt_trans zero_lt_one h) zero_lt_one },
    apply M_ih2,
    apply P_ih (P /ₘ X) h1; refl,
    apply P_ih (P /ₘ X + X),
    apply lt_of_le_of_lt (nat_degree_add_le _ X),
    rw [nat_degree_X, max_lt_iff],
    split; assumption },
end



/-
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
theorem my_poly_induction2 {F : Type u} [field F] {M : polynomial F → polynomial F → Prop} :
  (∀ (c : F) (P : polynomial F), M P (C c)) →
  (∀ P Q : polynomial F, M P Q → M Q P) →
  (∀ P Q R : polynomial F, R.nat_degree < Q.nat_degree → M R Q → M (P * R) Q → M (P * Q + R) Q) →
  ∀ P Q : polynomial F, M P Q :=
begin
  intros M_base M_ih1 M_ih2 P Q; revert Q P,
  refine polynomial_strong_induction_nat_degree _; intros Q Q_ih,
  cases nat.eq_zero_or_pos Q.nat_degree with h h,
  
  -- Base case: deg(Q) = 0
  { rw eq_C_of_nat_degree_eq_zero h,
    exact M_base (Q.coeff 0) },

  -- Induction step: deg(Q) > 0
  { refine polynomial_strong_induction_nat_degree _; intros P P_ih,
    cases lt_or_le P.nat_degree Q.nat_degree with h0 h0,

    -- Base case: deg(P) < deg(Q)
    exact M_ih1 _ _ (Q_ih P h0 Q),

    -- Induction step: deg(P) ≥ deg(Q)
    rw [← euclidean_domain.mod_add_div P Q, add_comm, mul_comm],
    by_cases h1 : P % Q = 0,

    -- Case Q | P
    { have h2 : M 0 Q := by rw ← C_0; exact M_ih1 _ _ (M_base 0 Q),
      rw h1; refine M_ih2 _ Q 0 _ h2 _,
      rw nat_degree_zero; exact h,
      rw mul_zero; exact h2 },

    -- Case Q ∤ P
    { have h2 : Q ≠ 0 := ne_zero_of_nat_degree_gt h,
      have h3 : (Q.leading_coeff)⁻¹ ≠ 0 := by apply inv_ne_zero; rwa leading_coeff_ne_zero,
      have h4 : (Q * C (Q.leading_coeff)⁻¹).monic := monic_mul_leading_coeff_inv h2,
      have h5 : (P % Q).nat_degree < Q.nat_degree,
      { rw [nat_degree_lt_nat_degree_iff h1, mod_def],
        exact lt_of_lt_of_eq (degree_mod_by_monic_lt _ h4) (degree_mul_C h3) },
      refine M_ih2 _ _ _ h5 (P_ih (P % Q) (lt_of_lt_of_le h5 h0)) _,
      apply P_ih,
      calc (P / Q * (P % Q)).nat_degree = (P / Q).nat_degree + (P % Q).nat_degree : _
      ... < (P / Q).nat_degree + Q.nat_degree : by rwa add_lt_add_iff_left
      ... = Q.nat_degree + (P / Q).nat_degree : by rw add_comm
      ... = Q.nat_degree + (P /ₘ _).nat_degree : by rw [div_def, nat_degree_C_mul h3]
      ... = Q.nat_degree + (P.nat_degree - (Q * _).nat_degree) : by rw nat_degree_div_by_monic _ h4
      ... = Q.nat_degree + (P.nat_degree - Q.nat_degree) : by rw nat_degree_mul_C h3
      ... = P.nat_degree : by rw [add_comm, nat.sub_add_cancel h0],
      { refine nat_degree_mul _ h1,
        intros h6,
        rw [div_def, mul_eq_zero, C_eq_zero, or_iff_right h3, div_by_monic_eq_zero_iff h4,
            degree_mul_C h3, ← nat_degree_lt_nat_degree_iff, lt_iff_not_le] at h6,
        exact absurd h0 h6,
        exact ne_zero_of_nat_degree_gt (lt_of_lt_of_le h h0) } } },
end



end extra
end IMO2017A6
