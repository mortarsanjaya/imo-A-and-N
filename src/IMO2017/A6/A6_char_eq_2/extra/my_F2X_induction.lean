import 
  data.zmod.basic
  data.polynomial.div

/-
  Implementation of induction necessary for results given in "poly_result.lean"
-/
namespace IMO2017A6

namespace extra

namespace my_F2X_induction

open polynomial



/-
  The elements of zmod 2 are just 0 and 1.
-/
lemma zmod2_elts :
  ∀ c : zmod 2, c = 0 ∨ c = 1 :=
begin
  intros c,
  cases c with x x_prop,
  rcases x with _ | x | x,
  left; refl,
  right; refl,
  rw [nat.succ_lt_succ_iff, nat.add_def, add_zero, nat.succ_lt_succ_iff] at x_prop,
  exfalso; exact nat.not_lt_zero x x_prop,
end



/-
  For any M : 𝔽₂[X] → Prop, M(P) holds for all P ∈ 𝔽₂[X] if all the following are true:
  1. M 0 and M X holds,
  2. For any P ∈ 𝔽₂[X], if M P holds, then M (P + 1) holds,
  3. For any P ∈ 𝔽₂[X], if M P and M (P + X) holds, then M (P * X) holds.
-/
theorem induction1 {M : polynomial (zmod 2) → Prop} :
  M 0 → M X →
    (∀ P : polynomial (zmod 2), M P → M (P + 1)) →
    (∀ P : polynomial (zmod 2), M P → M (P + X) → M (P * X)) →
    ∀ P : polynomial (zmod 2), M P :=
begin
  intros M_base1 M_base2 M_ih1 M_ih2 P,
  induction h : P.nat_degree using nat.strong_induction_on with n n_ih generalizing P,
  cases le_or_lt n 1 with h0 h0,

  -- Case n ≤ 1
  { rw ← h at h0,
    rw eq_X_add_C_of_nat_degree_le_one h0,
    suffices : M (C (P.coeff 1) * X),
    { cases zmod2_elts (P.coeff 0) with h1 h1,
      rwa [h1, map_zero, add_zero],
      rw [h1, map_one],
      exact M_ih1 _ this },
    cases zmod2_elts (P.coeff 1) with h1 h1,
    rwa [h1, map_zero, zero_mul],
    rwa [h1, map_one, one_mul] },

  -- Case 1 < n
  { rw [← mod_by_monic_add_div P monic_X, mod_by_monic_X, add_comm, mul_comm],
    suffices : M (P /ₘ X * X),
    { cases zmod2_elts (eval 0 P) with h1 h1,
      rwa [h1, map_zero, add_zero],
      rw [h1, map_one],
      exact M_ih1 _ this },
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





end my_F2X_induction

end extra

end IMO2017A6
