import IMO2020.N5.N5_extra.strong_map.basic

/-! # Some lemmas regarding strong maps -/

namespace IMOSL
namespace IMO2020N5

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} [fact p.prime]

private lemma pstrong_mod_p_induct (f : additive_map M) {a : ℕ} (h : good (p ^ a) f)
  {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) (h0 : k < p ^ a) : f k = f (k % p) :=
begin
  have hp := fact.out p.prime,
  rcases a.eq_zero_or_pos with rfl | h1,
  rw [pow_zero, nat.lt_one_iff] at h0,
  rw [h0, nat.zero_mod],
  revert hkp h0 k h; refine nat.le_induction _ _ a h1; clear h1 a,
  rw pow_one; intros h k hkp h0,
  rw nat.mod_eq_of_lt h0,
  intros n hn1 n_ih h k h0 h1,
  induction k using nat.strong_induction_on with k k_ih,
  cases lt_or_le k (p ^ n) with h2 h2,
  exact n_ih (good_factor f (pow_ne_zero _ hp.ne_zero) h ⟨p, pow_succ' p n⟩) h0 h2,
  clear n_ih,

  let c := p ^ (n + 1) / k,
  let d := p ^ (n + 1) % k,
  have X : ∀ a b : ℕ, b % a ≠ 0 ↔ ¬a ∣ b := λ a b, by rw [ne.def, nat.dvd_iff_mod_eq_zero],
  have hk : k ≠ 0 := by rintros rfl; exact h0 ⟨0, by rw mul_zero⟩,
  have hc : c ≠ 0 := ne_of_gt (nat.div_pos (le_of_lt h1) (zero_lt_iff.mpr hk)),
  have hd : d ≠ 0 := begin
    rw [X, nat.dvd_prime_pow hp]; rintros ⟨t, ht, rfl⟩,
    rw pow_le_pow_iff hp.one_lt at h2,
    replace h2 := pow_dvd_pow p (le_trans hn1 h2),
    rw pow_one at h2; exact h0 h2
  end,
  replace h2 : c < p :=
  begin
    rw le_iff_eq_or_lt at h2,
    rcases h2 with rfl | h2,
    exfalso; apply h0,
    replace hn1 := pow_dvd_pow p hn1,
    rwa pow_one at hn1,
    rwa [nat.div_lt_iff_lt_mul (zero_lt_iff.mpr hk), pow_succ, mul_lt_mul_left hp.pos]
  end,
  have h3 : c * k + d = p ^ (n + 1) := nat.div_add_mod' _ k,
  rw [← add_right_inj (f c), ← additive_map.map_mul_add f hc hk, h _ _ (mul_ne_zero hc hk) hd h3],
  replace h3 : p ∣ d + c * k := ⟨p ^ n, by rw [add_comm, h3, pow_succ]⟩,
  have h4 : ¬p ∣ c := nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr hc) h2,
  have h5 := nat.prime.not_dvd_mul hp h4 h0,
  have h6 : ¬p ∣ d := λ h6, by rw nat.dvd_add_right h6 at h3; exact h5 h3,
  have h7 : d < k := (p ^ (n + 1)).mod_lt (zero_lt_iff.mpr hk),
  replace k_ih := k_ih d h7 h6 (lt_trans h7 h1),
  replace h : good p f := good_factor f (pow_ne_zero _ hp.ne_zero) h ⟨p ^ n, by rw pow_succ⟩,
  rw [k_ih, ← nat.mod_eq_of_lt h2, ← good_prime_mul_mod_p f hp h h4 h0,
      h (c * k % p) (d % p) (by rwa X) (by rwa X)],
  rw [add_comm, ← nat.add_mod_add_of_le_add_mod, nat.mod_eq_zero_of_dvd h3, zero_add],
  exact nat.le_mod_add_mod_of_dvd_add_of_not_dvd h3 h6
end

open strong_map

theorem pstrong_mod_p (f : strong_map M p) {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) : f k = f (k % p) :=
  pstrong_mod_p_induct f (is_strong f k) hkp (nat.lt_pow_self (fact.out p.prime).one_lt k)

/-- This is an important lemma, but I do not know where to move it. -/
theorem pstrong_val (f : strong_map M p) {x : ℕ} (h : x ≠ 0) :
  f x = padic_val_nat p x • f p + f (ord_compl[p] x % p) :=
begin
  have hp := fact.out p.prime,
  rw [← pstrong_mod_p f (nat.not_dvd_ord_compl hp h), ← map_pow_smul f hp.ne_zero,
      ← map_mul_add f (pow_ne_zero _ hp.ne_zero) (ne_of_gt (nat.ord_compl_pos p h)),
      ← nat.factorization_def x hp, nat.ord_proj_mul_ord_compl_eq_self]
end

end IMO2020N5
end IMOSL
