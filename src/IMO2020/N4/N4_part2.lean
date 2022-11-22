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

variables {p : ℕ} (h : odd p)
include h

theorem balanced_iff_S0_coprime_eq_pairwise :
  balanced p ↔ ∀ x y : ℕ, x.coprime p → y.coprime p → S0 h x = S0 h y :=
begin
  ---- Right-to-left direction is easy
  symmetry; refine ⟨λ h1 a b ha hb h2, ⟨order_two_mod_p h, order_two_mod_p_pos h, _⟩, _⟩,
  rw [F_iterate_S, F_iterate_S, ← S0, ← S0, h1 a b ha hb, add_le_add_iff_right],
  exact le_of_lt h2,
  
  ---- Use contrapositive, and reduce to the case `S_p(x) < S_p(y)`
  suffices : (∃ x y : ℕ, x.coprime p ∧ y.coprime p ∧ S0 h x < S0 h y) → ¬balanced p,
  { intros h1; contrapose! h1,
    rcases h1 with ⟨x, y, h1, h2, h3⟩,
    rw [ne_iff_lt_or_gt, gt_iff_lt] at h3,
    cases h3 with h3 h3,
    exacts [this ⟨x, y, h1, h2, h3⟩, this ⟨y, x, h2, h1, h3⟩] },

  ---- There exists such `x` and `y` with an extra condition: `y < x`
  rintros ⟨u, y, h1, h2, h3⟩,
  simp only [balanced, not_forall, not_exists, not_and, not_le],
  replace h1 : ∃ x : ℕ, x.coprime p ∧ y < x ∧ S0 h x < S0 h y :=
  begin
    refine ⟨u + (y + 1) * p, _, _, _⟩,
    rwa nat.coprime_add_mul_right_left,
    rw ← nat.add_one_le_iff,
    exact le_trans (nat.le_mul_of_pos_right h.pos) le_add_self,
    rwa [S0_mod_p, nat.add_mul_mod_self_right, ← S0_mod_p]
  end,
  clear h3 u,
  rcases h1 with ⟨x, h1, h3⟩,

  ---- It suffices to find some `N ≥ 0` such that `F_p^N(x) > F_p^N(y)` but
  ----   `F_p^n(x) > F_p^n(y)` for all `n > N`
  suffices : ∃ N : ℕ, (∀ n : ℕ, N < n → (F p^[n]) x < (F p^[n]) y) ∧ (F p^[N]) y < (F p^[N]) x,
  { rcases this with ⟨N, h4, h5⟩,
    refine ⟨(F p^[N]) y, (F p^[N]) x, F_iterate_coprime h h2 _,
      F_iterate_coprime h h1 _, h5, λ k hk, _⟩,
    replace h4 := h4 (k + N) (lt_add_of_pos_left N hk),
    rwa [iterate_add, comp_app, comp_app] at h4 },

  ---- Finishing: find such `N`
  clear h1 h2; cases h3 with h1 h2,
  replace h2 := eventually_F_lt_of_S0_lt h h2,
  have h3 := nat.find_spec h2,
  refine ⟨(nat.find h2).pred, λ n X, h3 n (nat.le_of_pred_lt X), _⟩,
  generalize_hyp h4 : nat.find h2 = N at h3 ⊢,
  cases N with _ N,
  exact h1,
  refine lt_of_le_of_ne _ (λ X, ne_of_lt h1 (injective.iterate (F_injective h) _ X)),
  rw [nat.pred_succ, ← not_lt],
  replace h4 := nat.find_min h2 (by rw h4; exact N.lt_succ_self),
  clear h2,
  simp only [not_forall] at h4,
  rcases h4 with ⟨n, h2, h4⟩,
  rw [le_iff_eq_or_lt, ← nat.succ_le_iff] at h2,
  rcases h2 with rfl | h2,
  exact h4,
  exfalso; exact h4 (h3 n h2)
end

theorem balanced_iff_S0_coprime_eq_const (h0 : 1 < p) :
  balanced p ↔ ∀ x : ℕ, x.coprime p → 2 * S0 h x = order_two_mod_p h * p :=
begin
  ---- Right-to-left direction is again easy
  rw [balanced_iff_S0_coprime_eq_pairwise h, iff.comm],
  refine ⟨λ h1 x y h2 h3, _, λ h1 x h2, _⟩,
  replace h2 := h1 x h2,
  rw ← h1 y h3 at h2,
  exact nat.eq_of_mul_eq_mul_left two_pos h2,

  ---- Left-to-right direction is not too hard either
  suffices : ∃ y : ℕ, y.coprime p ∧ p ∣ x + y,
  { rcases this with ⟨y, h3, h4⟩,
    rw [← S0_p_dvd_add h (not_dvd_of_coprime (ne_of_gt h0) h2) h4, ← h1 x y h2 h3, ← two_mul] },
  clear h1 h0,
  refine ⟨x * (p - 1), h2.mul _, _⟩,
  cases p with _ p,
  exfalso; exact nat.lt_irrefl 0 h.pos,
  rw [nat.succ_eq_add_one, nat.add_sub_cancel, nat.coprime_self_add_right],
  exact nat.coprime_one_right p,
  rw [← mul_one_add, add_comm, nat.sub_add_cancel h.pos],
  exact ⟨x, mul_comm x p⟩
end

/-- Generally, if `-1` is a power of `2` mod `p`, then `p` is balanced -/
lemma balanced_of_neg_one_is_two_pow_mod_p (h0 : 1 < p) (h1 : ∃ c : ℕ, p ∣ 2 ^ c + 1) :
  balanced p :=
begin
  cases h1 with c h1,
  rw balanced_iff_S0_coprime_eq_const h h0; intros x h2,
  replace h1 : p ∣ x + 2 ^ c * x :=
    by rw [← one_add_mul, add_comm]; exact dvd_mul_of_dvd_left h1 x,
  rw [← S0_p_dvd_add h (not_dvd_of_coprime (ne_of_gt h0) h2) h1, S0_two_pow_mul h, ← two_mul]
end

/-- Generally, if `p` is balanced, then the order of `2` mod `p` is even -/
lemma even_order_two_mod_p_of_balanced (h0 : 1 < p) (h1 : balanced p) :
  even (order_two_mod_p h) :=
begin
  rw balanced_iff_S0_coprime_eq_const h h0 at h1,
  replace h1 : 2 ∣ order_two_mod_p h * p := ⟨S0 h 1, (h1 1 (nat.coprime_one_left p)).symm⟩,
  rwa [(two_coprime_p h).dvd_mul_right, ← even_iff_two_dvd] at h1
end

end general_results



section prime_results

/-- Final solution, part 2, prime power version -/
theorem final_solution_part2' {p : ℕ} (h : odd p) (h0 : is_prime_pow p) :
  balanced p ↔ even (order_two_mod_p h) :=
⟨even_order_two_mod_p_of_balanced h h0.one_lt,
  λ h1, balanced_of_neg_one_is_two_pow_mod_p h h0.one_lt
    ((order_two_even_iff_prime_pow h h0).mp h1)⟩

variables {p : ℕ} (hp : p.prime)
include hp

/-- Final solution, part 2 -/
theorem final_solution_part2 (h : odd p) :
  balanced p ↔ even (order_two_mod_p h) :=
  final_solution_part2' h hp.is_prime_pow

/-- If p is prime, p ≡ 3 or 5 (mod 8), then p is balanced -/
theorem balanced_3_or_5_mod_8 (h : p % 8 = 3 ∨ p % 8 = 5) : balanced p :=
begin
  have h0 : p ≠ 2 := by contrapose! h; subst h; split; norm_num,
  have h1 : odd p := (or_iff_right h0).mp hp.eq_two_or_odd',
  refine balanced_of_neg_one_is_two_pow_mod_p h1 hp.one_lt ⟨p / 2, _⟩,
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
