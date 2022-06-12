import
  data.polynomial.basic
  data.polynomial.div
  field_theory.ratfunc

/-
  Implementation of induction necessary for results given in "poly_result.lean"
-/
namespace IMO2017A6

namespace extra

open polynomial
open ratfunc



universe u

/-
  Let R be a non-trivial commutative ring.
  For any M : R[X] → Prop, M(P) holds for all P ∈ R[X] if all the following are true:
  (1). For any c ∈ R, M(cX) holds,
  (2). For any P ∈ R[X] and c ∈ R, if M(P) holds, then M(P + c) holds,
  (3). For any P ∈ R[X], if M(P) and M(P + X) holds, then M(P * X) holds.

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
  intros M_base M_ih1 M_ih2 P,
  induction h : P.nat_degree using nat.strong_induction_on with n n_ih generalizing P,
  cases le_or_lt n 1 with h0 h0,

  -- Case n ≤ 1 (Base Case)
  { rw ← h at h0,
    rw eq_X_add_C_of_nat_degree_le_one h0,
    apply M_ih1,
    exact M_base (P.coeff 1) },
  
  -- Case 1 < n (Induction Step)
  { rw [← mod_by_monic_add_div P monic_X, mod_by_monic_X, add_comm, mul_comm],
    apply M_ih1,
    have h1 : (P /ₘ X).nat_degree < n,
    { rw [nat_degree_div_by_monic P monic_X, nat_degree_X, h],
      exact nat.sub_lt (lt_trans zero_lt_one h0) zero_lt_one },
    apply M_ih2,
    { apply n_ih (P /ₘ X).nat_degree h1; refl },
    { apply n_ih (P /ₘ X + X).nat_degree,
      work_on_goal 2 { refl },
      apply lt_of_le_of_lt (nat_degree_add_le _ X),
      rw [nat_degree_X, max_lt_iff],
      split; assumption } },
end



end extra

end IMO2017A6
