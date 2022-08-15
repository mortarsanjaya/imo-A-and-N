import IMO2020.N5.N5_extra.additive_map data.nat.factorization.basic data.nat.modeq

/-!
# Good maps

Let `f : ℕ → α` be a function, where `α` is an arbitrary type.
We say that `f` is `n`-*good* for some positive integer `n` if
  `f(k) = f(n - k)` for all positive integers `k < n`.
We say that `f` is *wide* if `f` is `p`-good for infinitely many `p` prime.
We say that `f` is `p`-*strong* for some `p : ℕ` if `f` is `p^k`-good for all `k ≥ 0`.

For convenience, we define the terminologies with respect any function `f : ℕ → α`.
However, we are only going to prove results for additive maps on commutative cancellative monoids.
Also, this file only proves results for good maps.
The main results are as follows:
* `f` is `n`-good for infinitely many `n` iff it is either wide or `p`-strong for some prime `p`.
* If `f` is `p`-good for a prime `p`, then `f(km % p) = f(k) + f(m)` for any `0 < k, m < p`.
-/

namespace IMOSL
namespace IMO2020N5

open additive_map
open_locale classical



section defs

variables {α : Type*}

def good (n : ℕ) (f : ℕ → α) := ∀ a b : ℕ, 0 < a → 0 < b → a + b = n → f a = f b
def wide (f : ℕ → α) := {p : ℕ | p.prime ∧ good p f}.infinite
def strong (p : ℕ) (f : ℕ → α) := ∀ k : ℕ, good (p ^ k) f

end defs



section results

variables {M : Type*} [add_cancel_comm_monoid M] (f : additive_map M)

lemma good_one : good 1 f :=
begin
  rintros a b ha hb h,
  exfalso; refine ne_of_gt _ h,
  rw ← nat.succ_le_iff at ha hb ⊢,
  exact add_le_add ha hb
end

lemma good_zero : good 0 f :=
begin
  rintros a b ha hb h,
  exfalso; exact ne_of_gt (add_pos ha hb) h
end

lemma good_factor {n : ℕ} (h : 0 < n) (h0 : good n f) {d : ℕ} (h1 : d ∣ n) : good d f :=
begin
  rcases h1 with ⟨c, rfl⟩,
  rcases c.eq_zero_or_pos with rfl | hc,
  exfalso; rw mul_zero at h; exact lt_irrefl 0 h,
  intros a b ha hb h1,
  replace h0 := h0 (a * c) (b * c) (mul_pos ha hc) (mul_pos hb hc) (by rw [← add_mul, h1]),
  rwa [map_mul_add f ha hc, map_mul_add f hb hc, add_left_inj] at h0
end

private lemma general1 {p : ℕ} (hp : p.prime) (h : ¬strong p f) :
  ∃ c : ℕ, ∀ k : ℕ, good (p ^ k) f ↔ k ≤ c :=
begin
  simp only [strong, not_exists, not_forall] at h,
  set c := nat.find h with hc,
  have h1 : ¬good (p ^ c) f := nat.find_spec h,
  clear_value c; cases c with c c,
  rw pow_zero at h1,
  exfalso; exact h1 (good_one f),
  refine ⟨c, λ k, ⟨λ h0, _, λ h0, _⟩⟩,
  { rw [← not_lt, ← nat.succ_le_iff]; intros h2,
    exact h1 (good_factor f (pow_pos hp.pos _) h0 (pow_dvd_pow p h2)) },
  { refine not_not.mp (nat.find_min h _),
    rwa [← hc, nat.lt_succ_iff] }
end

private lemma general2 (h : ∀ (p : ℕ) (hp : p.prime), ¬strong p f) : ∃ x : ℕ → ℕ,
  (∀ p : ℕ, x p ≠ 0 → p.prime) ∧ ∀ (p : ℕ) (hp : p.prime) (k : ℕ), good (p ^ k) f ↔ k ≤ x p :=
begin
  have h0 : ∀ p : nat.primes, ∃ kp : ℕ, (∀ k : ℕ, good (p ^ k) f ↔ k ≤ kp) :=
    λ ⟨p, hp⟩, by rw subtype.coe_mk; exact general1 f hp (h p hp),
  replace h0 := classical.axiom_of_choice h0,
  cases h0 with x h0,
  refine ⟨(λ p, dite p.prime (λ hp : p.prime, x ⟨p, hp⟩) (λ _, 0)), (λ p h1, _), (λ p hp k, _)⟩,
  contrapose! h1; rw dif_neg h1,
  change good (p ^ k) f with good (↑(⟨p, hp⟩ : nat.primes) ^ k) f,
  rw [dif_pos hp, h0]
end

private lemma general3 (h : ¬wide f) (h0 : ∀ (p : ℕ) (hp : p.prime), ¬strong p f) : ∃ x : ℕ →₀ ℕ,
  (∀ p : ℕ, x p ≠ 0 → p.prime) ∧ ∀ (p : ℕ) (hp : p.prime) (k : ℕ), good (p ^ k) f ↔ k ≤ x p :=
begin
  simp only [wide, set.not_infinite] at h,
  replace h0 := general2 f h0; rcases h0 with ⟨x, h0, h1⟩,
  refine ⟨⟨h.to_finset, x, (λ p, _)⟩, ⟨h0, h1⟩⟩,
  rw [set.finite.mem_to_finset, set.mem_set_of_eq]; split,
  { rintros ⟨h2, h3⟩,
    replace h1 := h1 p h2 1,
    rw pow_one at h1,
    rwa [h1, nat.succ_le_iff, zero_lt_iff] at h3 },
  { intros h2,
    have h3 := h0 p h2,
    replace h1 := h1 p h3 1,
    rw [pow_one, nat.succ_le_iff, zero_lt_iff] at h1,
    rw h1; exact ⟨h3, h2⟩ }
end
  
theorem good_infinite_iff_wide_or_strong : {p : ℕ | good p f}.infinite ↔
  wide f ∨ ∃ {p : ℕ} (hp : p.prime), strong p f :=
begin
  refine ⟨(λ h, _), _⟩,
  { contrapose! h,
    rw set.not_infinite,
    replace h := general3 f h.1 h.2,
    rcases h with ⟨x, h, h0⟩,
    suffices : ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, good n f → n = 0 ∨ n ∣ N,
    { rcases this with ⟨N, hN, this⟩,
      refine set.finite.subset (finset.range N.succ).finite_to_set (λ n h0, _),
      rw [finset.mem_coe, finset.mem_range, nat.lt_succ_iff],
      rcases this n h0 with rfl | h0,
      exacts [N.zero_le, nat.le_of_dvd hN h0] },
    use x.prod has_pow.pow,
    rw and_iff_left_of_imp,
    { refine nat.prod_pow_pos_of_zero_not_mem_support (λ h1, _),
      rw finsupp.mem_support_iff at h1,
      exact nat.not_prime_zero (h 0 h1) },
    { intros h1 n h2,
      rcases eq_or_ne n 0 with rfl | h3,
      left; refl,
      rw [or_iff_right h3, ← nat.factorization_le_iff_dvd h3 (ne_of_gt h1),
          nat.prod_pow_factorization_eq_self (by simp; exact h), finsupp.le_iff],
      rintros p h4,
      replace h4 : p.prime := nat.prime_of_mem_factorization h4,
      rw [nat.factorization_def n h4, ← h0 p h4],
      exact good_factor f (zero_lt_iff.mpr h3) h2 pow_padic_val_nat_dvd } },
  { rintros (h | ⟨p, hp, h⟩),
    refine set.infinite.mono (λ x h0, _) h; exact h0.2,
    exact set.infinite_of_injective_forall_mem (nat.pow_right_injective hp.two_le) h }
end

private lemma general7 {p : ℕ} (hp : p.prime) (h : good p f) {k m : ℕ}
  (kpos : 0 < k) (hkp : k < p) (mpos : 0 < m) (hmp : m < p) : f (k * m % p) = f k + f m :=
begin
  revert m mpos hmp; induction k using nat.strong_induction_on with k k_ih; intros m mpos hmp,
  induction m using nat.strong_induction_on with m m_ih,
  cases lt_or_le (k * m) p with h0 h0,
  rw [nat.mod_eq_of_lt h0, map_mul_add f kpos mpos],
  let c := p / m,
  let d := p % m,
  have X : ∀ a b : ℕ, 0 < b % a ↔ ¬a ∣ b :=
    λ a b, by rw [zero_lt_iff, ne.def, nat.dvd_iff_mod_eq_zero],

  have dpos : 0 < d :=
  begin
    rw X; intros h1,
    rw [← nat.succ_le_iff, le_iff_eq_or_lt, eq_comm] at mpos,
    rcases mpos with rfl | mpos,
    rw mul_one at h0; exact not_le_of_lt hkp h0,
    replace mpos := nat.min_fac_le_of_dvd mpos h1,
    rw nat.prime.min_fac_eq hp at mpos; exact not_le_of_lt hmp mpos
  end,
  replace m_ih : f (k * d % p) = f k + f d :=
    m_ih d (p.mod_lt mpos) dpos (lt_trans (p.mod_lt mpos) hmp),
  have cpos : 0 < c :=
    by rw [zero_lt_iff, ne.def, nat.div_eq_zero_iff mpos]; exact lt_asymm hmp,
  replace h0 : c < k :=
  begin
    rw le_iff_lt_or_eq at h0,
    rcases h0 with h0 | rfl,
    rwa nat.div_lt_iff_lt_mul mpos,
    simp only [d, nat.mul_mod_left, not_lt_zero'] at dpos,
    exfalso; exact dpos
  end,
  replace k_ih := @k_ih c h0 cpos (lt_trans h0 hkp),
  have h1 : c * m + d = p := nat.div_add_mod' p m,
  have h2 : ∀ n : ℕ, 0 < n → n < p → ¬p ∣ n := λ n, nat.not_dvd_of_pos_of_lt,
  have hcp := lt_trans h0 hkp,
  have hdp := lt_trans (p.mod_lt mpos) hmp,
  replace hkp := h2 k kpos hkp,
  replace hmp := h2 m mpos hmp,
  have hkcmp := hp.not_dvd_mul hkp (hp.not_dvd_mul (h2 c cpos hcp) hmp),
  rw [← add_left_inj (f c), add_assoc, add_comm (f m), add_comm,
      ← map_mul_add f cpos mpos, h _ d (mul_pos cpos mpos) dpos h1,
      ← m_ih, ← k_ih (by rw X; exact hp.not_dvd_mul hkp hmp) (nat.mod_lt _ hp.pos),
      ← nat.mod_eq_of_lt hcp, ← nat.mul_mod, mul_left_comm],
  refine h _ _ _ _ _,
  rw X; exact hkcmp,
  rw X; refine hp.not_dvd_mul hkp (h2 d dpos hdp),
  rw [← nat.add_mod_add_of_le_add_mod, ← mul_add, h1, nat.mul_mod_left, zero_add],
  refine nat.le_mod_add_mod_of_dvd_add_of_not_dvd _ hkcmp,
  rw [← mul_add, h1, mul_comm]; use k
end

theorem good_prime_mul_mod_p {p : ℕ} (hp : p.prime) (h : good p f) {k m : ℕ}
  (hkp : ¬p ∣ k) (hmp : ¬p ∣ m) : f (k * m % p) = f (k % p) + f (m % p) :=
begin
  rw [nat.dvd_iff_mod_eq_zero, ← ne.def, ← zero_lt_iff] at hkp hmp,
  rw [← general7 f hp h hkp (k.mod_lt hp.pos) hmp (m.mod_lt hp.pos), ← nat.mul_mod]
end

theorem good_prime_pow_mod_p {p : ℕ} (hp : p.prime) (h : good p f)
  {k : ℕ} (hkp : ¬p ∣ k) (t : ℕ) : f (k ^ t % p) = t • f (k % p) :=
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
