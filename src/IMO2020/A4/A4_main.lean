import analysis.mean_inequalities data.multiset.fintype IMO2020.A4.A4_general

/-! # IMO 2020 A4 (P2) -/

namespace IMOSL
namespace IMO2020A4

open multiset

/- ### General extra lemmas -/

/-- The specialized multiset version of AM-GM: `∏ x^x ≤ ∑ x * x` -/
lemma multiset_weighted_AM_GM_specialized_mul_self {S : multiset ℝ}
  (h : ∀ x : ℝ, x ∈ S → 0 ≤ x) (h0 : S.sum = 1) :
  (S.map $ λ x : ℝ, x ^ x).prod ≤ (S.map $ λ x : ℝ, x * x).sum :=
  (congr_arg multiset.prod (S.map_univ _).symm).trans_le $
  (congr_arg multiset.sum $ S.map_univ _).le.trans' $
  real.geom_mean_le_arith_mean_weighted (finset.univ : finset ↥S) coe coe
    (λ x _, h _ coe_mem) (S.sum_eq_sum_coe.symm.trans h0) (λ x _, h _ coe_mem)

/-- The specialized multiset version of AM-GM: `∏ x^x ≤ ∑ x^2` -/
lemma multiset_weighted_AM_GM_specialized_sq {S : multiset ℝ}
  (h : ∀ x : ℝ, x ∈ S → 0 ≤ x) (h0 : S.sum = 1) :
  (S.map $ λ x : ℝ, x ^ x).prod ≤ (S.map $ λ x : ℝ, x ^ 2).sum :=
  (multiset_weighted_AM_GM_specialized_mul_self h h0).trans_eq $
    congr_arg sum $ map_congr rfl $ λ x _, (sq x).symm

/-- Specialized multiset version of AM-GM but with a stronger hypothesis -/
lemma multiset_weighted_AM_GM_specialized' {S : multiset ℝ}
  (h : ∀ x : ℝ, x ∈ S → 0 < x) (h0 : S.sum = 1) :
  (S.map $ λ x : ℝ, x ^ x).prod ≤ (S.map $ λ x : ℝ, x ^ 2).sum :=
  multiset_weighted_AM_GM_specialized_sq (λ x, all_le_of_all_lt h) h0

/-- Power of sum equals product of power, `multiset ℝ` version -/
lemma multiset_rpow_sum_of_pos {a : ℝ} (h : 0 < a) (S : multiset ℝ) :
  (S.map $ pow a).prod = a ^ S.sum :=
  multiset.induction_on S a.rpow_zero.symm $
    λ x S h0, by rw [map_cons, prod_cons, h0, sum_cons, real.rpow_add h]





/- ### Start of the problem -/

section generalized

variables {a : ℝ} (h : 0 < a) {S : multiset ℝ} (h0 : ∀ x : ℝ, x ∈ S → 0 < x)

private lemma two_mul_lt_three (h1 : a + S.sum = 1) : 2 * a < 3 :=
  two_mul_lt_three_of_le_one $ le_of_add_multiset_sum_eq (λ x, all_le_of_all_lt h0) h1

variables (h1 : ∀ x : ℝ, x ∈ S → x ≤ a) (h2 : a + S.sum = 1)
include h h0 h1 h2

lemma power_bound : ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod ≤ a :=
suffices ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod ≤ ((a ::ₘ S).map $ pow a).prod,
  from this.trans_eq $ (multiset_rpow_sum_of_pos h _).trans $
    h2.symm.trans (S.sum_cons a).symm ▸ a.rpow_one,
multiset_ring_prod_map_le_prod_map _ _
  (forall_mem_cons.mpr $ let h3 : ∀ b : ℝ, 0 < b → 0 ≤ b ^ b :=
    λ b h3, (b.rpow_pos_of_pos h3).le in ⟨h3 a h, λ x h4, h3 x $ h0 x h4⟩)
  (forall_mem_cons.mpr ⟨le_refl _, λ x h3,
    let h4 : 0 ≤ x := (h0 x h3).le in real.rpow_le_rpow h4 (h1 x h3) h4⟩)

lemma AM_GM_bound : ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod ≤ a ^ 2 + (1 - a) ^ 2 :=
  (multiset_weighted_AM_GM_specialized'
    (forall_mem_cons.mpr ⟨h, h0⟩) ((S.sum_cons a).trans h2)).trans $
  (S.map_cons (λ x : ℝ, x ^ 2) a).symm ▸ (sum_cons _ _).trans_le $
  add_le_add_left ((multiset_sum_sq_le_sq_sum $ λ x, all_le_of_all_lt h0).trans_eq $
    congr_arg2 _ (eq_sub_of_add_eq' h2) rfl) (a ^ 2)

lemma AM_GM_bound_strict (h3 : 1 < S.card) :
  ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod < a ^ 2 + (1 - a) ^ 2 :=
  (multiset_weighted_AM_GM_specialized'
    (forall_mem_cons.mpr ⟨h, h0⟩) ((S.sum_cons a).trans h2)).trans_lt $
  (S.map_cons (λ x : ℝ, x ^ 2) a).symm ▸ (sum_cons _ _).trans_lt $
  add_lt_add_left ((multiset_sum_sq_lt_sq_sum_of_pos h3 h0).trans_eq $
    congr_arg2 _ (eq_sub_of_add_eq' h2) rfl) (a ^ 2)

lemma case_a_lt_half (h3 : 2 * a < 1) :
  (3 - 2 * a) * ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod < 1 :=
  (ring_ineq1 h3).trans_le' $ mul_le_mul_of_nonneg_left (power_bound h h0 h1 h2) $
    sub_nonneg_of_le (two_mul_lt_three h0 h2).le

lemma case_a_ne_half_ne_one (h3 : 2 * a ≠ 1) (h4 : a ≠ 1) :
  (3 - 2 * a) * ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod < 1 :=
  h3.lt_or_lt.elim (case_a_lt_half h h0 h1 h2) $ λ h3,
  (ring_ineq3 h3 h4).trans_le' $ mul_le_mul_of_nonneg_left (AM_GM_bound h h0 h1 h2) $
    sub_nonneg_of_le (two_mul_lt_three h0 h2).le

lemma case_S_card_big (h3 : 1 < S.card) :
  (3 - 2 * a) * ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod < 1 :=
  (lt_or_le (2 * a) 1).elim (case_a_lt_half h h0 h1 h2) $ λ h4,
    (ring_ineq2 h4).trans_lt' $ mul_lt_mul_of_pos_left (AM_GM_bound_strict h h0 h1 h2 h3) $
    sub_pos_of_lt $ two_mul_lt_three h0 h2





/- ### Final solutions -/

/-- Final solution, main inequality -/
theorem final_solution_main_ineq :
  (3 - 2 * a) * ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod ≤ 1 :=
(lt_or_le (2 * a) 1).elim
---- Case 1: `2a < 1`
(λ h3, (case_a_lt_half h h0 h1 h2 h3).le)
---- Case 2: `2a ≥ 1`
(λ h3, (ring_ineq2 h3).trans' $ mul_le_mul_of_nonneg_left (AM_GM_bound h h0 h1 h2) $
  sub_nonneg.mpr $ (le_add_of_nonneg_right zero_le_one).trans' $
  mul_le_of_le_one_right zero_le_two $ h2.le.trans' $ le_add_of_nonneg_right $
  sum_nonneg $ λ x, all_le_of_all_lt h0)

/-- Final solution, equality case -/
theorem final_solution_eq_case :
  (3 - 2 * a) * ((a ::ₘ S).map $ λ x : ℝ, x ^ x).prod = 1 ↔ 
    (a = 1 ∧ S = 0) ∨ (a = 2⁻¹ ∧ S = {2⁻¹}) :=
---- `→` direction
⟨λ h3, S.card.eq_zero_or_pos.imp
  -- `|S| = 0`
  (λ h4, let h5 : S = 0 := card_eq_zero.mp h4 in ⟨by rwa [h5, sum_zero, add_zero] at h2, h5⟩)
  -- `|S| ≥ 1`
  (λ h4, begin
    rw [← nat.succ_le_iff, le_iff_lt_or_eq] at h4,
    cases h4 with h4 h4,
    exact absurd h3 (case_S_card_big h h0 h1 h2 h4).ne,
    rw [eq_comm, card_eq_one] at h4; rcases h4 with ⟨b, rfl⟩,
    cases ne_or_eq (2 * a) 1 with h4 h4,
    { refine absurd h3 (case_a_ne_half_ne_one h h0 h1 h2 h4 $ λ h5, _).ne,
      rw [h5, sum_singleton, add_right_eq_self] at h2,
      revert h2; exact (h0 b $ mem_singleton_self b).ne.symm },
    { have h5 : a = (2 : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right h4,
      refine ⟨h5, congr_arg _ _⟩,
      rwa [sum_singleton, ← h4, two_mul, add_right_inj, h5] at h2 }
  end),
---- `←` direction
λ h3, h3.elim
  -- `a = 1` and `S = 0`
  (λ h3, by rw [h3.1, h3.2, cons_zero, map_singleton, prod_singleton, mul_one,
    bit1, add_sub_cancel', one_mul, real.rpow_one])
  -- `a = 2⁻¹` and `S = {2⁻¹}`
  (λ h3, let h4 : 0 < (2 : ℝ) := zero_lt_two, h5 := mul_inv_cancel h4.ne.symm in
    by rw [h3.1, h3.2, h5, bit1, add_sub_cancel, map_cons, map_singleton, prod_cons,
      prod_singleton, ← real.rpow_add (inv_pos.mpr h4), ← two_mul, h5, real.rpow_one, h5])⟩

end generalized





/-- Final solution, original version -/
theorem final_solution_original {a b c d : ℝ}
  (h : 0 < d) (h0 : d ≤ c) (h1 : c ≤ b) (h2 : b ≤ a) (h3 : a + (b + (c + d)) = 1) :
  (a + (2 * b + (3 * c + 4 * d))) * (a ^ a * (b ^ b * (c ^ c * d ^ d))) < 1 :=
begin
  rw [← prod_singleton (d ^ d), ← map_singleton (λ x : ℝ, x ^ x)],
  iterate 3 { rw [← prod_cons, ← map_cons (λ x : ℝ, x ^ x)] },
  have h4 : 0 < a := h.trans_le (h0.trans $ h1.trans h2),
  have h5 : ∀ x : ℝ, x ∈ b ::ₘ c ::ₘ {d} → 0 < x := let h6 := h.trans_le h0 in
    forall_mem_cons.mpr ⟨h6.trans_le h1, forall_mem_cons.mpr
      ⟨h6, λ x h7, h.trans_eq (mem_singleton.mp h7).symm⟩⟩,
  refine (mul_le_mul_of_nonneg_right _ _).trans_lt (case_S_card_big h4 h5 _ _ _),
  ---- `a + 2b + 3c + 4d ≤ 3 - 2a`
  { exact (ring_ineq4 a b c d $ h0.trans h1).trans_eq
      (congr_arg2 _ (h3.symm ▸ mul_one _) rfl) },
  ---- `0 ≤ a^a b^b c^c d^d`, multiset product version
  { refine prod_nonneg (λ x h6, _),
    rw mem_map at h6; rcases h6 with ⟨y, h6, rfl⟩,
    exact y.rpow_nonneg_of_nonneg
      ((mem_cons.mp h6).elim (λ h7, h4.trans_eq h7.symm) (h5 y)).le },
  ---- For each `x ∈ {b, c, d}`, we have `x ≤ a`
  { refine forall_mem_cons.mpr ⟨h2, forall_mem_cons.mpr _⟩,
    have h5 := h1.trans h2,
    exact ⟨h5, λ x h6, (mem_singleton.mp h6).trans_le (h0.trans h5)⟩ },
  ---- `a + {b, c, d}.sum = 1`
  { rwa [sum_cons, sum_cons, sum_singleton] },
  ---- `|{b, c, d}| > 1`
  { exact nat.succ_lt_succ (nat.succ_pos 1) }
end

end IMO2020A4
end IMOSL
