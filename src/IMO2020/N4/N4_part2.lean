import
  IMO2020.N4.N4_basic
  number_theory.legendre_symbol.quadratic_reciprocity
  extra.number_theory.dirichlet_thm_arithmetic_progression

/-! # IMO 2020 N4, Generalized Version (Part 2) -/

namespace IMOSL
namespace IMO2020N4

open function
open_locale classical

def balanced (p : ℕ) := ∀ a b : ℕ,
  a.coprime p → b.coprime p → a < b → ∃ i : ℕ, 0 < i ∧ (F p^[i]) a ≤ (F p^[i]) b



section general_results

variables {p : ℕ} (h : odd p) (h0 : 1 < p)
include h h0

private lemma lem1 :
  balanced p ↔ ∀ x y : ℕ, x.coprime p → y.coprime p → S0 h x = S0 h y :=
begin
  -- Right-to-left direction is easy
  symmetry; refine ⟨λ h1 a b ha hb h2, ⟨order_two_mod_p h, order_two_mod_p_pos h, _⟩, _⟩,
  rw [F_iterate_S, F_iterate_S, ← S0, ← S0, h1 a b ha hb, add_le_add_iff_right],
  exact le_of_lt h2,
  
  -- Use contrapositive, and reduce to the case `S_p(x) < S_p(y)`
  suffices : (∃ x y : ℕ, x.coprime p ∧ y.coprime p ∧ S0 h x < S0 h y) → ¬balanced p,
  { intros h1; contrapose! h1,
    rcases h1 with ⟨x, y, h1, h2, h3⟩,
    rw [ne_iff_lt_or_gt, gt_iff_lt] at h3,
    cases h3 with h3 h3,
    exacts [this ⟨x, y, h1, h2, h3⟩, this ⟨y, x, h2, h1, h3⟩] },

  -- There exists such `x` and `y` with an extra condition: `y < x`
  rintros ⟨u, y, h1, h2, h3⟩,
  simp only [balanced, not_forall, not_exists, not_and, not_le],
  replace h1 : ∃ x : ℕ, x.coprime p ∧ y < x ∧ S0 h x < S0 h y :=
  begin
    refine ⟨u + (y + 1) * p, _, _, _⟩,
    rwa nat.coprime_add_mul_right_left,
    rw ← nat.add_one_le_iff,
    exact le_trans (nat.le_mul_of_pos_right (lt_trans one_pos h0)) le_add_self,
    rwa [S0_mod_p, nat.add_mul_mod_self_right, ← S0_mod_p]
  end,

  -- `S_p(x) < S_p(y)` means there exists a maximal `N ≥ 0` respecting `F_p^N(y) < F_p^N(x)`.
  clear h3 u; rcases h1 with ⟨x, h1, h3, h4⟩,
  replace h4 : ∃ N : ℕ, (∀ n : ℕ, N < n → (F p^[n]) x < (F p^[n]) y) ∧ (F p^[N]) y < (F p^[N]) x :=
  begin
    replace h4 := main_lemma h h4,
    replace h1 := nat.find_spec h4,
    replace h2 : 0 < nat.find h4 :=
      by simp only [nat.find_pos, not_forall]; exact ⟨0, le_refl 0, lt_asymm h3⟩,
    refine ⟨(nat.find h4).pred, λ n h3, h1 n _, _⟩,
    rwa [← nat.succ_le_iff, nat.succ_pred_eq_of_pos h2] at h3,
    replace h0 := nat.find_min h4 (nat.pred_lt (ne_of_gt h2)),
    simp only [not_forall] at h0,
    rcases h0 with ⟨c, h5, h6⟩,
    rw [le_iff_lt_or_eq, ← nat.succ_le_iff, nat.succ_pred_eq_of_pos h2] at h5,
    rcases h5 with h5 | rfl,
    exfalso; exact h6 (h1 c h5),
    rw [not_lt, le_iff_lt_or_eq] at h6,
    cases h6 with h6 h6,
    exact h6,
    exfalso; refine ne_of_lt h3 (injective.iterate (F_injective h) _ h6)
  end,

  -- Finishing
  rcases h4 with ⟨N, h4, h5⟩,
  refine ⟨(F p^[N]) y, (F p^[N]) x, F_iterate_coprime h h2 _,
    F_iterate_coprime h h1 _, h5, λ k hk, _⟩,
  replace h4 := h4 (k + N) (lt_add_of_pos_left N hk),
  rwa [iterate_add, comp_app, comp_app] at h4
end

private lemma lem2 :
  balanced p ↔ ∀ x : ℕ, x.coprime p → 2 * S0 h x = order_two_mod_p h * p :=
begin
  rw lem1 h h0; refine ⟨λ h1 x h2, _, λ h1 x y h2 h3, _⟩,
  { obtain ⟨y, h3, h4⟩ : ∃ y : ℕ, y.coprime p ∧ p ∣ x + y :=
    begin
      refine ⟨x * (p - 1), h2.mul _, _⟩,
      cases p with _ p,
      exfalso; exact lt_asymm one_pos h0,
      rw [nat.succ_eq_add_one, nat.add_sub_cancel, nat.coprime_self_add_right],
      exact nat.coprime_one_right p,
      rw [← mul_one_add, add_comm, nat.sub_add_cancel (le_of_lt h0)],
      exact ⟨x, mul_comm x p⟩
    end,
    rw [← S0_p_dvd_add h _ h4, ← h1 x y h2 h3, ← two_mul],
    rintros ⟨d, rfl⟩,
    replace h2 := h2.coprime_mul_right,
    rw nat.coprime_self at h2,
    exact ne_of_gt h0 h2 },
  { replace h2 := h1 x h2,
    rw ← h1 y h3 at h2,
    exact nat.eq_of_mul_eq_mul_left two_pos h2 }
end

/-- Generally, if -1 is a power of 2 mod p, then p is balanced -/
private lemma lem3 (h1 : ∃ c : ℕ, p ∣ 2 ^ c + 1) : balanced p :=
begin
  cases h1 with c h1,
  rw lem2 h h0; intros x h2,
  rw [← @S0_p_dvd_add p h x (2 ^ c * x), S0_two_pow_mul h, ← two_mul],
  { rintros ⟨d, rfl⟩,
    replace h2 := h2.coprime_mul_right,
    rw nat.coprime_self at h2,
    exact ne_of_gt h0 h2 },
  { rw [← one_add_mul, add_comm],
    exact dvd_mul_of_dvd_left h1 x }
end

/-- Generally, if p is balanced, then the order of 2 mod p is even -/
private lemma lem4 (h1 : balanced p) : even (order_two_mod_p h) :=
begin
  rw lem2 h h0 at h1,
  replace h1 : 2 ∣ order_two_mod_p h * p := ⟨S0 h 1, (h1 1 (nat.coprime_one_left p)).symm⟩,
  rwa [(two_coprime_p h).dvd_mul_right, ← even_iff_two_dvd] at h1
end

end general_results



section prime_results

variables {p : ℕ} (hp : p.prime)
include hp

/-- Final solution, part 2 -/
theorem final_solution_part2 (h : odd p) : balanced p ↔ even (order_two_mod_p h) :=
begin
  refine ⟨lem4 h hp.one_lt, λ h0, lem3 h hp.one_lt _⟩,
  rw even_iff_two_dvd at h0,
  cases h0 with c h0; use c,
  have h1 := order_two_mod_p_pos h,
  rw [h0, zero_lt_mul_left (two_pos : 0 < 2)] at h1,
  have h2 := p_dvd_two_pow_sub_one_iff h,
  rw h0 at h2; clear h0,
  have h0 := (h2 (2 * c)).mpr (dvd_refl (2 * c)),
  change p ∣ _ - 1 ^ 2 at h0,
  rw [mul_comm, pow_mul, nat.sq_sub_sq, hp.dvd_mul] at h0,
  cases h0 with h0 h0,
  exact h0,
  rw [← one_mul c, h2, nat.mul_dvd_mul_iff_right h1] at h0,
  exfalso; revert h0,
  rw [← even_iff_two_dvd, imp_false, ← nat.odd_iff_not_even],
  exact odd_one
end

/-- If p is prime, p ≡ 3 or 5 (mod 8), then p is balanced -/
theorem balanced_3_or_5_mod_8 (h : p % 8 = 3 ∨ p % 8 = 5) : balanced p :=
begin
  have h0 : p ≠ 2 := by contrapose! h; subst h; split; norm_num,
  have h1 : odd p := (or_iff_right h0).mp hp.eq_two_or_odd',
  refine lem3 h1 hp.one_lt ⟨p / 2, _⟩,
  haveI : fact p.prime := ⟨hp⟩,
  have h2 := h0,
  rw [← nat.coprime_primes hp nat.prime_two, hp.coprime_iff_not_dvd,
      ← char_p.cast_eq_zero_iff (zmod p), nat.cast_two, ← int.cast_two] at h2,
  cases legendre_sym.eq_one_or_neg_one p h2 with h3 h3,
  rw [legendre_sym.eq_one_iff p h2, int.cast_two, zmod.exists_sq_eq_two_iff h0] at h3,
  exfalso; contrapose! h,
  cases h3 with h3 h3; rw h3; norm_num,
  rw [← char_p.cast_eq_zero_iff (zmod p), nat.cast_succ, add_eq_zero_iff_eq_neg,
      nat.cast_pow, nat.cast_two, ← int.cast_two, ← legendre_sym.eq_pow, h3,
      int.cast_neg, int.cast_one]
end

/-- If p is prime, p ≡ 7 (mod 8), then p is not balanced -/
theorem not_balanced_7_mod_8 (h : p % 8 = 7) : ¬balanced p :=
begin
  have h0 : p ≠ 2 := by contrapose! h; subst h; norm_num,
  have h1 : odd p := (or_iff_right h0).mp hp.eq_two_or_odd',
  rw [final_solution_part2 hp h1, ← nat.odd_iff_not_even],
  suffices : 2 ^ (p / 2) ≡ 1 [MOD p],
  { rw two_pow_mod_p_eq_one_iff h1 at this,
    cases this with c this,
    refine @nat.odd.of_mul_left _ c _,
    rw ← this; clear this c,
    rw [← nat.div_add_mod p 8, h, bit0, ← two_mul, mul_assoc, add_comm,
        nat.add_mul_div_left _ _ two_pos, nat.odd_add],
    norm_num },

  haveI : fact p.prime := ⟨hp⟩,
  rw [← zmod.eq_iff_modeq_nat, nat.cast_one, nat.cast_pow, nat.cast_two,
      ← zmod.euler_criterion, zmod.exists_sq_eq_two_iff h0],
  right; exact h,
  rwa [ne.def, ← nat.cast_two, char_p.cast_eq_zero_iff (zmod p) p,
       ← hp.coprime_iff_not_dvd, nat.coprime_primes hp nat.prime_two]
end

end prime_results





/-- There are infinitely many odd primes that are not balanced.
  This is the original version of Part 2. -/
theorem infinite_set_of_odd_primes_not_balanced :
  {p : ℕ | odd p ∧ p.prime ∧ ¬balanced p}.infinite :=
begin
  have h : 7 < 8 := by norm_num,
  have h0 : nat.coprime 7 8 := by norm_num,
  refine set.infinite.mono _ (extra.infinite_set_of_primes_mod_eq h h0),
  rintros p ⟨hp, h1⟩,
  refine ⟨_, hp, not_balanced_7_mod_8 hp h1⟩,
  refine (or_iff_right _).mp hp.eq_two_or_odd',
  contrapose! h1; subst h1; norm_num
end

/-- There are also infinitely many odd primes that are balanced. -/
theorem infinite_set_of_odd_primes_balanced :
  {p : ℕ | odd p ∧ p.prime ∧ balanced p}.infinite :=
begin
  have h : 5 < 8 := by norm_num,
  have h0 : nat.coprime 5 8 := by norm_num,
  refine set.infinite.mono _ (extra.infinite_set_of_primes_mod_eq h h0),
  rintros p ⟨hp, h1⟩,
  refine ⟨_, hp, balanced_3_or_5_mod_8 hp (or.inr h1)⟩,
  refine (or_iff_right _).mp hp.eq_two_or_odd',
  contrapose! h1; subst h1; norm_num
end

end IMO2020N4
end IMOSL
