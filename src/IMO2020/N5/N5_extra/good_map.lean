import IMO2020.N5.N5_extra.additive_map

/-!
# Good maps

Let `f : additive_map M` be an additive map, where `M` is an additive commutative monoid.
We say that `f` is `n`-good for some positive integer `n` if `f(k) = f(n - k)` for all `0 < k < n`.
We say that `f` is wide if `f` is `p`-good for infinitely many `p` prime.
We say that `f` is `p`-strong for some fixed prime `p` if `f` is `p^k`-good for all `k ≥ 0`.

This file provides all the above definitions, but only proves results for good maps.
The main results are as follows:
* `f` is `n`-good for infinitely many `n` iff it is either wide or `p`-strong for some prime `p`.
* If `f` is `p`-good for a prime `p`, then `f(km % p) = f(k) + f(m)` for any `0 < k, m < p`.

TODO: Prove all the above results.
-/

namespace IMOSL
namespace IMO2020N5

open additive_map
open_locale classical



section defs

variables {M : Type*} [add_comm_monoid M]

def good (n : ℕ) (f : additive_map M) := ∀ a b : ℕ, 0 < a → 0 < b → a + b = n → f a = f b
def wide (f : additive_map M) := {p : ℕ | p.prime ∧ good p f}.infinite
def strong {p : ℕ} (hp : p.prime) (f : additive_map M) := ∀ k : ℕ, good (p ^ k) f

end defs



section results

variables {M : Type*} [add_cancel_comm_monoid M] (f : additive_map M)

private lemma general1 : good 1 f :=
begin
  rintros a b ha hb h,
  exfalso; refine ne_of_gt _ h,
  rw ← nat.succ_le_iff at ha hb ⊢,
  exact add_le_add ha hb
end

private lemma general2 : good 0 f :=
begin
  rintros a b ha hb h,
  exfalso; exact ne_of_gt (add_pos ha hb) h
end

private lemma general3 {n : ℕ} (h : 0 < n) (h0 : good n f) {d : ℕ} (h1 : d ∣ n) : good d f :=
begin
  rcases h1 with ⟨c, rfl⟩,
  rcases c.eq_zero_or_pos with rfl | hc,
  exfalso; rw mul_zero at h; exact lt_irrefl 0 h,
  intros a b ha hb h1,
  replace h0 := h0 (a * c) (b * c) (mul_pos ha hc) (mul_pos hb hc) (by rw [← add_mul, h1]),
  rwa [map_mul_add f ha hc, map_mul_add f hb hc, add_left_inj] at h0
end

private lemma general4 {p : ℕ} (hp : p.prime) (h : ¬strong hp f) :
  ∃ c : ℕ, ∀ k : ℕ, good (p ^ k) f ↔ k ≤ c :=
begin
  simp only [strong, not_exists, not_forall] at h,
  set c := nat.find h with hc,
  have h1 : ¬good (p ^ c) f := nat.find_spec h,
  clear_value c; cases c with c c,
  rw pow_zero at h1,
  exfalso; exact h1 (general1 f),
  refine ⟨c, λ k, ⟨λ h0, _, λ h0, _⟩⟩,
  { rw [← not_lt, ← nat.succ_le_iff]; intros h2,
    exact h1 (general3 f (pow_pos hp.pos _) h0 (pow_dvd_pow p h2)) },
  { refine not_not.mp (nat.find_min h _),
    rwa [← hc, nat.lt_succ_iff] }
end

private lemma general5 (h : ∀ (p : ℕ) (hp : p.prime), ¬strong hp f) : ∃ x : ℕ → ℕ,
  (∀ p : ℕ, x p ≠ 0 → p.prime) ∧ ∀ (p : ℕ) (hp : p.prime) (k : ℕ), good (p ^ k) f ↔ k ≤ x p :=
begin
  have h0 : ∀ p : nat.primes, ∃ kp : ℕ, (∀ k : ℕ, good (p ^ k) f ↔ k ≤ kp) :=
    λ ⟨p, hp⟩, by rw subtype.coe_mk; exact general4 f hp (h p hp),
  replace h0 := classical.axiom_of_choice h0,
  cases h0 with x h0; simp only [] at h0,
  refine ⟨(λ p, dite p.prime (λ hp : p.prime, x ⟨p, hp⟩) (λ _, 0)), (λ p h1, _), (λ p hp k, _)⟩,
  contrapose! h1; rw dif_neg h1,
  change good (p ^ k) f with good (↑(⟨p, hp⟩ : nat.primes) ^ k) f,
  rw [dif_pos hp, h0]
end

private lemma general6 (h : ¬wide f) (h0 : ∀ (p : ℕ) (hp : p.prime), ¬strong hp f) : ∃ x : ℕ →₀ ℕ,
  (∀ p : ℕ, x p ≠ 0 → p.prime) ∧ ∀ (p : ℕ) (hp : p.prime) (k : ℕ), good (p ^ k) f ↔ k ≤ x p :=
begin
  simp only [wide, set.not_infinite] at h,
  replace h0 := general5 f h0; rcases h0 with ⟨x, h0, h1⟩,
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
  wide f ∨ ∃ {p : ℕ} (hp : p.prime), strong hp f :=
begin
  refine ⟨(λ h, _), _⟩,
  { contrapose! h,
    rw set.not_infinite,
    replace h := general6 f h.1 h.2,
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
      exact general3 f (zero_lt_iff.mpr h3) h2 pow_padic_val_nat_dvd } },
  { rintros (h | ⟨p, hp, h⟩),
    refine set.infinite.mono (λ x h0, _) h; exact h0.2,
    exact set.infinite_of_injective_forall_mem (nat.pow_right_injective hp.two_le) h }
end

private theorem good_prime_mul_mod_p {p : ℕ} (hp : p.prime) (h : good p f)
  {k m : ℕ} (hkp : ¬p ∣ k) (hmp : ¬p ∣ m) : f ((k * m) % p) = f (k % p) + f (m % p) :=
begin
  sorry
end

private theorem good_prime_pow_mod_p {p : ℕ} (hp : p.prime) (h : good p f)
  {k : ℕ} (hkp : ¬p ∣ k) (t : ℕ) : f ((k ^ t) % p) = t • f (k % p) :=
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
