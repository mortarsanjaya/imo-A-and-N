import IMO2020.N5.N5_extra.good_map data.nat.log data.nat.modeq

/-!
# `p`-strong maps

We characterize `p`-strong maps.
As it turns out, they are precisely the functions that can be described as
  `p^k t ↦ kc + χ(t mod p)` for some `c : M` and `χ : (zmod p)ˣ → M` where
  `χ` is a map with `χ(ab) = χ(a) χ(b)` for any `a b : (zmod p)ˣ` and `χ(-1) = 1`.
Alternatively, using a bijection `(zmod (p / 2)) → additive (zmod p)ˣ/⟨-1⟩`,
  we can replace `χ` with a map `(zmod (p / 2)) →+ M`.
-/

namespace IMOSL
namespace IMO2020N5

open additive_map
open_locale classical



variables {M : Type*} [add_cancel_comm_monoid M] (f : additive_map M)

private lemma pstrong_mod_p_induct {p : ℕ} (hp : p.prime) {a : ℕ} (h : good (p ^ a) f)
  {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) (h0 : k < p ^ a) : f k = f (k % p) :=
begin
  rcases a.eq_zero_or_pos with rfl | h1,
  rw [pow_zero, nat.lt_one_iff] at h0,
  rw [h0, nat.zero_mod],
  revert hkp h0 k h; refine nat.le_induction _ _ a h1; clear h1 a,
  rw pow_one; intros h k hkp h0,
  rw nat.mod_eq_of_lt h0,
  intros n hn1 n_ih h k h0 h1,
  induction k using nat.strong_induction_on with k k_ih,
  cases lt_or_le k (p ^ n) with h2 h2,
  exact n_ih (good_factor f (pow_pos hp.pos _) h ⟨p, pow_succ' p n⟩) h0 h2,
  clear n_ih,

  let c := p ^ (n + 1) / k,
  let d := p ^ (n + 1) % k,
  have X : ∀ a b : ℕ, 0 < b % a ↔ ¬a ∣ b :=
    λ a b, by rw [zero_lt_iff, ne.def, nat.dvd_iff_mod_eq_zero],
  have kpos : 0 < k := by rw zero_lt_iff; rintros rfl; exact h0 ⟨0, by rw mul_zero⟩,
  have cpos : 0 < c := nat.div_pos (le_of_lt h1) kpos,
  have dpos : 0 < d := begin
    rw [X, nat.dvd_prime_pow hp],
    rintros ⟨t, ht, rfl⟩,
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
    rwa [nat.div_lt_iff_lt_mul kpos, pow_succ, mul_lt_mul_left hp.pos]
  end,
  have h3 : c * k + d = p ^ (n + 1) := nat.div_add_mod' _ k,
  rw [← add_right_inj (f c), ← map_mul_add f cpos kpos, h _ _ (mul_pos cpos kpos) dpos h3],
  replace h3 : p ∣ d + c * k := ⟨p ^ n, by rw [add_comm, h3, pow_succ]⟩,
  have h4 : ¬p ∣ c := nat.not_dvd_of_pos_of_lt cpos h2,
  have h5 := nat.prime.not_dvd_mul hp h4 h0,
  have h6 : ¬p ∣ d := λ h6, by rw nat.dvd_add_right h6 at h3; exact h5 h3,
  have h7 : d < k := (p ^ (n + 1)).mod_lt kpos,
  replace k_ih := k_ih d h7 h6 (lt_trans h7 h1),
  replace h : good p f := good_factor f (pow_pos hp.pos _) h ⟨p ^ n, by rw pow_succ⟩,
  rw [k_ih, ← nat.mod_eq_of_lt h2, ← good_prime_mul_mod_p f hp h h4 h0,
      h (c * k % p) (d % p) (by rwa X) (by rwa X)],
  rw [add_comm, ← nat.add_mod_add_of_le_add_mod, nat.mod_eq_zero_of_dvd h3, zero_add],
  exact nat.le_mod_add_mod_of_dvd_add_of_not_dvd h3 h6
end



variables {p : ℕ} (hp : p.prime) (h : strong hp f)
include hp h

theorem pstrong_mod_p {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) : f k = f (k % p) :=
  pstrong_mod_p_induct f hp (h k) hkp (nat.lt_pow_self hp.one_lt k)



end IMO2020N5
end IMOSL
