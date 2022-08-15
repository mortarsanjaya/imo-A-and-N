import IMO2020.N5.N5_extra.strong_map_basic data.nat.log data.nat.modeq data.zmod.basic

/-!
# Characterization of `p`-strong maps

We characterize `p`-strong additive maps, where `p` is a prime.
As it turns out, they are precisely the functions that can be described as
  `p^k t ↦ kc + χ(t mod p)` for some `c : M` and `χ : (zmod p)ˣ → M` where
  `χ` is a map with `χ(ab) = χ(a) χ(b)` for any `a b : (zmod p)ˣ` and `χ(-1) = 1`.
Alternatively, using a bijection `(zmod (p / 2)) → additive (zmod p)ˣ/⟨-1⟩`
  for odd `p`, we can replace `χ` with a map `(zmod (p / 2)) →+ M`.

TODO:

1. Construct the "natural" `p`-strong map `M →+ additive_map M`.
We will call it the `p`-type map.
2. Construct the homomorphism `(zmod (p / 2)) → additive (zmod p)ˣ/⟨-1⟩` for `p` odd.
3. Construct the `p`-strong map `((zmod (p / 2)) →+ M) →+ additive_map M`.
We will call it the `coprime`-type map.
4. Construct the `p`-strong map `(M × ((zmod (p / 2) →+ M)) →+ additive_map M`.
The map is obtained by combining a `p`-type and `coprime`-type map.
5. Construct the bijection between `strong_map M p` and `M × (zmod (p / 2)`.
-/

namespace IMOSL
namespace IMO2020N5

open additive_map



section extra_lemmas

private lemma padic_add_eq_p_pow' (p : ℕ) [fact (p.prime)] {a b k : ℕ}
  (ha : 0 < a) (hb : 0 < b) (h : a + b = p ^ k) : padic_val_nat p a ≤ padic_val_nat p b :=
begin
  suffices : ∀ n : ℕ, p ^ n ∣ a → p ^ n ∣ b,
  { replace this := this (padic_val_nat p a) pow_padic_val_nat_dvd,
    rwa [padic_val_nat_dvd_iff, or_iff_right (ne_of_gt hb)] at this },
  intros n h0,
  rw [nat.dvd_add_iff_right h0, h, nat.pow_dvd_pow_iff_le_right (fact.out p.prime).one_lt],
  refine le_of_lt (lt_of_not_le (λ h1, _)),
  rw [← nat.pow_dvd_pow_iff_le_right (fact.out p.prime).one_lt, ← h] at h1,
  replace h0 := nat.le_of_dvd ha (dvd_trans h1 h0),
  rw [add_le_iff_nonpos_right, ← not_lt] at h0,
  exact h0 hb
end

lemma padic_add_eq_p_pow (p : ℕ) [fact (p.prime)] {a b k : ℕ}
  (ha : 0 < a) (hb : 0 < b) (h : a + b = p ^ k) : padic_val_nat p a = padic_val_nat p b :=
  le_antisymm (padic_add_eq_p_pow' p ha hb h) (padic_add_eq_p_pow' p hb ha (by rwa add_comm))

end extra_lemmas







section additive_map

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} (hp : p.prime) (f : additive_map M)
include hp

private lemma pstrong_mod_p_induct {a : ℕ} (h : good (p ^ a) f)
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

private theorem pstrong_mod_p (h : strong p f) {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) : f k = f (k % p) :=
  pstrong_mod_p_induct hp f (h k) hkp (nat.lt_pow_self hp.one_lt k)

end additive_map



section strong_map

/- ... -/

end strong_map

end IMO2020N5
end IMOSL
