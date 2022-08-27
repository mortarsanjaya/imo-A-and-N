import IMO2020.N5.N5_extra.additive_map extra.number_theory.divisor_closed_prop data.nat.modeq

/-!
# Good maps

Let `f : ℕ → α` be a function, where `α` is an arbitrary type.
We say that a `n : ℕ` is `f`-*good* if `f(k) = f(n - k)` for all positive integers `k < n`.
The main result is as follows.
* Let `M` be a commutative cancellative monoid and `f : ℕ → M` be an additive map.
If a prime `p` is `f`-good, then `f(km % p) = f(k) + f(m)` for any `0 < k, m < p`.
-/

namespace IMOSL
namespace IMO2020N5

open additive_map extra
open_locale classical



def good {α : Type*} (f : ℕ → α) (n : ℕ) := ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → a + b = n → f a = f b



section results

variables {M : Type*} [add_cancel_comm_monoid M] (f : additive_map M)

/-- `1` is always `f`-good. -/
lemma good_one : good f 1 :=
begin
  rintros a b ha hb h,
  rw ← zero_lt_iff at ha hb,
  exfalso; refine ne_of_gt _ h,
  rw ← nat.succ_le_iff at ha hb ⊢,
  exact add_le_add ha hb
end

/-- `0` is always `f`-good. -/
lemma good_zero : good f 0 :=
  λ a b ha hb h, by exfalso; exact ha (add_eq_zero_iff.mp h).left

/-- The `f`-good predicate is divisor-closed. -/
lemma good_dc : divisor_closed (good f) :=
begin
  rintros n h h0 d ⟨c, rfl⟩,
  rcases eq_or_ne c 0 with rfl | hc,
  exfalso; exact h d.mul_zero,
  intros a b ha hb h1,
  replace h0 := h0 _ _ (mul_ne_zero ha hc) (mul_ne_zero hb hc) (by rw [← add_mul, h1]),
  rwa [map_mul_add f ha hc, map_mul_add f hb hc, add_left_inj] at h0
end

/-- The `f`-good predicate is infinite iff it is either `wide` or `p`-strong for some prime `p`. -/
theorem good_infinite_iff_wide_or_strong :
  (set_of (good f)).infinite ↔ wide (good f) ∨ ∃ p : ℕ, p.prime ∧ strong p (good f) :=
  dc_infinite_iff_wide_or_strong (good_dc f)

/-- The main result. -/
theorem good_prime_mul_lt_p {p : ℕ} (hp : p.prime) (h : good f p) {k m : ℕ}
  (hk : k ≠ 0) (hkp : k < p) (hm : m ≠ 0) (hmp : m < p) : f (k * m % p) = f k + f m :=
begin
  revert m hm hmp; induction k using nat.strong_induction_on with k k_ih; intros m hm hmp,
  induction m using nat.strong_induction_on with m m_ih,
  cases lt_or_le (k * m) p with h0 h0,
  rw [nat.mod_eq_of_lt h0, map_mul_add f hk hm],
  let c := p / m,
  let d := p % m,
  have X : ∀ a b : ℕ, b % a ≠ 0 ↔ ¬a ∣ b :=
    λ a b, by rw [ne.def, nat.dvd_iff_mod_eq_zero],

  have hd : d ≠ 0 :=
  begin
    rw X; intros h1,
    rw [← zero_lt_iff, ← nat.succ_le_iff, le_iff_eq_or_lt, eq_comm] at hm,
    rcases hm with rfl | hm,
    rw mul_one at h0; exact not_le_of_lt hkp h0,
    replace hm := nat.min_fac_le_of_dvd hm h1,
    rw nat.prime.min_fac_eq hp at hm; exact not_le_of_lt hmp hm
  end,
  rw ← zero_lt_iff at hm,
  replace m_ih : f (k * d % p) = f k + f d :=
    m_ih d (p.mod_lt hm) hd (lt_trans (p.mod_lt hm) hmp),
  have hc : c ≠ 0 :=
    by rw [ne.def, nat.div_eq_zero_iff hm]; exact lt_asymm hmp,
  replace h0 : c < k :=
  begin
    rw le_iff_lt_or_eq at h0,
    rcases h0 with h0 | rfl,
    rwa nat.div_lt_iff_lt_mul hm,
    simp only [d, nat.mul_mod_left, not_lt_zero'] at hd,
    exfalso; exact hd rfl
  end,
  replace k_ih := @k_ih c h0 hc (lt_trans h0 hkp),
  have h1 : c * m + d = p := nat.div_add_mod' p m,
  have h2 : ∀ n : ℕ, n ≠ 0 → n < p → ¬p ∣ n :=
    λ n hn0, nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr hn0),
  have hcp := lt_trans h0 hkp,
  have hdp := lt_trans (p.mod_lt hm) hmp,
  replace hkp := h2 k hk hkp,
  rw zero_lt_iff at hm,
  replace hmp := h2 m hm hmp,
  have hkcmp := hp.not_dvd_mul hkp (hp.not_dvd_mul (h2 c hc hcp) hmp),
  rw [← add_left_inj (f c), add_assoc, add_comm (f m), add_comm,
      ← map_mul_add f hc hm, h _ d (mul_ne_zero hc hm) hd h1,
      ← m_ih, ← k_ih (by rw X; exact hp.not_dvd_mul hkp hmp) (nat.mod_lt _ hp.pos),
      ← nat.mod_eq_of_lt hcp, ← nat.mul_mod, mul_left_comm],
  refine h _ _ _ _ _,
  rw X; exact hkcmp,
  rw X; refine hp.not_dvd_mul hkp (h2 d hd hdp),
  rw [← nat.add_mod_add_of_le_add_mod, ← mul_add, h1, nat.mul_mod_left, zero_add],
  refine nat.le_mod_add_mod_of_dvd_add_of_not_dvd _ hkcmp,
  rw [← mul_add, h1, mul_comm]; use k
end

/-- The main result, but given completely in modulo `p`. -/
theorem good_prime_mul_mod_p {p : ℕ} (hp : p.prime) (h : good f p) {k m : ℕ}
  (hkp : ¬p ∣ k) (hmp : ¬p ∣ m) : f (k * m % p) = f (k % p) + f (m % p) :=
begin
  rw [nat.dvd_iff_mod_eq_zero, ← ne.def] at hkp hmp,
  rw [← good_prime_mul_lt_p f hp h hkp (k.mod_lt hp.pos) hmp (m.mod_lt hp.pos), ← nat.mul_mod]
end

/-- A corollary of `good_prime_mul_mod_p` with power in place of multiplication. -/
theorem good_prime_pow_mod_p {p : ℕ} (hp : p.prime) (h : good f p) {k : ℕ} (hkp : ¬p ∣ k) (t : ℕ) :
  f (k ^ t % p) = t • f (k % p) :=
begin
  induction t with t t_ih,
  rw [zero_smul, pow_zero, nat.mod_eq_of_lt hp.one_lt, additive_map.map_one_zero],
  rw [nat.succ_eq_add_one, pow_succ', add_smul, one_smul,
      good_prime_mul_mod_p f hp h _ hkp, t_ih],
  rw ← nat.prime.coprime_iff_not_dvd hp at hkp ⊢,
  exact nat.coprime.pow_right t hkp
end

end results



end IMO2020N5
end IMOSL
