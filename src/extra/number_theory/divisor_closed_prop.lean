import data.nat.factorization.basic

/-!
# Divisor-closed proposition

We say that a predicate `P : ℕ → Prop` is divisor-closed if for any positive
  integer `n` for which `P(n)` holds, we also have `P(d)` for any factor `d` of `n`. 
We also define the following terminologies; most of their purposes are in number theory problems.
* We say that `P` is *wide* if `P(p)` holds for infinitely many primes `p`.
* We say that `P` is *`p`-strong* for some `p : ℕ` if `P(p^k)` holds for any `k ≥ 0`.
We defined `p`-strong generally to avoid complications.
However, its main usage comes when `p` is prime.

For convenience, we say that `P` is infinite if `P(n)` holds for infinitely many `n : ℕ`.
The main result we will prove is that a divisor-closed predicate `P` is
  infinite if and only if  `P` is either wide or `p`-strong for some prime `p`.
Note that we need axiom of choice to prove this result.

**Proof**

Clearly wide and `p`-strong predicates for any `p ≥ 2` are infinite.
Thus, it remains to prove the converse.
Let `P` be a divisor-closed predicate.
Suppose that `P` is neither wide or `p`-strong for any `p` prime.
Note that, if `P(n)` holds for some `n`, then `P(1)` must hold since `P` is divisor-closed.
Thus it is clear that `P` is not infinite if `P(1)` does not hold.
For the rest of the proof, we assume that `P(1)` holds.

For each `p` prime, since `P` is divisor-closed but not `p`-strong, there exists
  `x_p : ℕ` such that `P(p^k) ↔ k ≤ x_p` for any `k : ℕ`.
Indeed, we just take the maximum `k` such that `P(p^k)` holds.
Axiom of choice gives us a map `x : p ↦ x_p` with the domain being the set of primes.
Now, since `P` is not wide, `P(p)`, equivalently `x_p ≥ 1`, holds for finitely many primes `p`.

Finally, let `N = ∏ p, p^{x_p}`; the product is taken over primes `p` for which `x_p ≥ 1`.
If a positive integer `n` does not divide `N`, then `x_p < ν_p(n)` for some `p` prime.
Then `P(p^{ν_p(n)})` does not hold, so `P(n)` does not hold either.
Thus, for any `n` such that `P(n)` holds, we necessarily have `n ∣ N`.
There are finitely many such `n`, so `P` is not infinite, as desired.
-/

namespace IMOSL
namespace extra

/-- Divisor-closed maps -/
def divisor_closed (P : ℕ → Prop) := ∀ n : ℕ, n ≠ 0 → P n → ∀ d : ℕ, d ∣ n → P d

/-- Wide maps -/
def wide (P : ℕ → Prop) := {p : ℕ | p.prime ∧ P p}.infinite

/-- `p`-strong maps -/
def strong (p : ℕ) (P : ℕ → Prop) := ∀ k : ℕ, P (p ^ k)



section results

/-- If `P` is wide, then `P(n)` holds for infinitely many `n`,
  even if `P` is not divisor-closed. -/
theorem infinite_pred_of_wide {P : ℕ → Prop} (h0 : wide P) : (set_of P).infinite :=
  h0.mono (λ x h1, h1.2)

/-- If `P` is `p`-strong for some `p ≥ 2`, not necessarily prime, then
  `P(n)` holds for infinitely many `n`, even if `P` is not divisor-closed. -/
theorem infinite_pred_of_strong {P : ℕ → Prop} {p : ℕ} (h0 : 2 ≤ p) (h1 : strong p P) :
  (set_of P).infinite :=
  set.infinite_of_injective_forall_mem (nat.pow_right_injective h0) h1



variables {P : ℕ → Prop} [decidable_pred P] (h : divisor_closed P)
include h

/-- If `P(n)` holds for some `n ≠ 0`, then `P(1)` holds; this is obvious. -/
lemma dc_at_one {n : ℕ} (h0 : n ≠ 0) (h1 : P n) : P 1 :=
  h n h0 h1 1 (one_dvd n)

/-- An if-and-only-if criterion for a divisor-closed predicate to be `p`-strong; `p ≠ 0`. -/
theorem dc_not_strong_iff {p : ℕ} (h0 : p ≠ 0) :
  ¬strong p P ↔ (∃ c : ℕ, ∀ k : ℕ, P (p ^ k) ↔ k < c) :=
  not_forall.trans
  ⟨λ h1, ⟨nat.find h1, λ k,
    ⟨λ h2, lt_of_not_le $ λ h3, nat.find_spec h1 $
      h _ (pow_ne_zero k h0) h2 _ (pow_dvd_pow _ h3),
    λ h2, not_not.mp $ nat.find_min h1 h2⟩⟩,
  λ h1, exists.elim h1 $ λ c h2, ⟨c, λ h3, (lt_irrefl c).elim $ (h2 c).mp h3⟩⟩

/-- Using choice, given a predicate `P` that is not `p`-strong for any `p` prime, construct a
  map `x : nat.primes → ℕ` such that `P(p^k) → k < x_p` for any `k : ℕ` and `p` prime. -/
theorem dc_not_strong_aoc_map_iff (h0 : ∀ p : ℕ, p.prime → ¬strong p P) :
  ∃ x : ℕ → ℕ, (∀ p : ℕ, x p ≠ 0 → p.prime) ∧
    ∀ (p : ℕ) (hp : p.prime) (k : ℕ), P (p ^ k) ↔ k < x p :=
begin
  have h1 : ∀ p : nat.primes, ∃ kp : ℕ, (∀ k : ℕ, P (p ^ k) ↔ k < kp) :=
    λ ⟨p, hp⟩, by rw [subtype.coe_mk, ← dc_not_strong_iff h hp.ne_zero]; exact h0 p hp,
  replace h1 := classical.axiom_of_choice h1,
  cases h1 with x h1,
  refine ⟨(λ p, dite p.prime (λ hp : p.prime, x ⟨p, hp⟩) (λ _, 0)), (λ p h2, _), (λ p hp k, _)⟩,
  rw [ne.def, dite_eq_right_iff, not_forall] at h2,
  cases h2 with h2 _; exact h2,
  rw [dif_pos hp, ← h1, subtype.coe_mk]
end

/-- Using choice, given a predicate `P` that is not `p`-strong for any `p` prime, construct a
  map `x : nat.primes → ℕ` such that `P(p^k) → k ≤ x_p` for any `k : ℕ` and `p` prime.
This is just a weak version of `dc_not_strong_aoc_map_iff`. -/
theorem dc_not_strong_aoc_map (h0 : ∀ p : ℕ, p.prime → ¬strong p P) :
  ∃ x : ℕ → ℕ, (∀ p : ℕ, x p ≠ 0 → p.prime) ∧
    ∀ (p : ℕ) (hp : p.prime) (k : ℕ), P (p ^ k) → k ≤ x p :=
  exists.elim (dc_not_strong_aoc_map_iff h h0) $
    λ x h1, ⟨x, h1.1, λ p hp k h2, le_of_lt $ (h1.2 p hp k).mp h2⟩

/-- Using choice, given a predicate `P` that is not `p`-strong for any `p` prime, under the
  condition `P(1)`, construct a map `x : nat.primes → ℕ` such that `P(p^k) ↔ k ≤ x_p` for any
  `k : ℕ` and `p` prime. -/
theorem dc_not_strong_aoc_map_iff' (h0 : ∀ p : ℕ, p.prime → ¬strong p P) (h1 : P 1) :
  ∃ x : ℕ → ℕ, (∀ p : ℕ, x p ≠ 0 → p.prime) ∧
    ∀ (p : ℕ) (hp : p.prime) (k : ℕ), P (p ^ k) ↔ k ≤ x p :=
begin
  rcases dc_not_strong_aoc_map_iff h h0 with ⟨x, h2, h3⟩,
  refine ⟨λ p, x p - 1, λ p h4, h2 p (λ h5, _), λ p hp k, _⟩,
  rw h5 at h4; exact h4 rfl,
  rw [h3 p hp, ← nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel],
  rwa [nat.succ_le_iff, ← h3 p hp, pow_zero]
end

/-- Using choice, given a predicate `P` that is neither wide nor `p`-strong for any `p` prime,
  under the condition `P(1)`, construct a finitely-supported map `x : nat.primes → ℕ` such that
  `P(p^k) ↔ k ≤ x_p` for any `k : ℕ` and `p` prime. -/
theorem dc_not_wide_strong_aoc_finsupp
    (h0 : ¬wide P) (h1 : ∀ p : ℕ, p.prime → ¬strong p P) (h2 : P 1) :
  ∃ x : ℕ →₀ ℕ, (∀ p : ℕ, x p ≠ 0 → p.prime) ∧
    ∀ (p : ℕ) (hp : p.prime) (k : ℕ), P (p ^ k) ↔ k ≤ x p :=
begin
  rw [wide, set.not_infinite] at h0,
  replace h2 := dc_not_strong_aoc_map_iff' h h1 h2,
  clear h h1; rcases h2 with ⟨x, h, h1⟩,
  refine ⟨⟨h0.to_finset, x, (λ p, _)⟩, ⟨h, h1⟩⟩,
  rw [set.finite.mem_to_finset, set.mem_set_of_eq, iff.comm],
  refine ⟨λ h2, ⟨h p h2, _⟩, λ h2, _⟩,
  rwa [← pow_one p, h1 p (h p h2), nat.succ_le_iff, zero_lt_iff],
  rw [← zero_lt_iff, ← nat.succ_le_iff, ← h1 p h2.1, pow_one],
  exact h2.2
end

/-- Assuming choice, if `P(n)` holds for infinitely many `n`, then
  `P` is either wide or `p`-strong for some `p` prime. -/
theorem dc_wide_or_strong_of_infinite (h0 : (set_of P).infinite) :
  wide P ∨ ∃ p : ℕ, p.prime ∧ strong p P :=
begin
  ---- First find `x : primes →₀ ℕ` such that `P(n) → ∀ p, v_p(n) ≤ x_p`
  have h1 : P 1 := by rcases h0.exists_gt 0 with ⟨n, h1, h2⟩;
    exact dc_at_one h (ne_of_gt h2) h1,
  by_contra' h2; replace h2 := dc_not_wide_strong_aoc_finsupp h h2.1 h2.2 h1,
  clear h1; rcases h2 with ⟨x, h1, h2⟩,

  ---- Now take any `m > ∏_p p^{x_p}` and get a contradiction
  replace h0 := h0.exists_gt (x.prod has_pow.pow),
  rcases h0 with ⟨m, h0, h3⟩,
  revert h3; rw [imp_false, not_lt],
  cases eq_or_ne m 0 with h3 h3,
  rw h3; exact (x.prod pow).zero_le,
  have h4 : 0 < x.prod pow := nat.prod_pow_pos_of_zero_not_mem_support
    (λ h4, nat.not_prime_zero (h1 0 $ finsupp.mem_support_iff.mp h4)),
  refine nat.le_of_dvd h4 _,
  rw [← nat.factorization_le_iff_dvd h3 (ne_of_gt h4),
      nat.prod_pow_factorization_eq_self _, finsupp.le_iff],
  intros p h5; replace h5 : p.prime := nat.prime_of_mem_factorization h5,
  rw [nat.factorization_def m h5, ← h2 p h5],
  exact h m h3 h0 _ pow_padic_val_nat_dvd,
  intros p h5; exact h1 p (finsupp.mem_support_iff.mp h5)
end

/-- Assuming choice, `P(n)` holds for infinitely many `n` iff
  `P` is either wide or `p`-strong for some `p` prime. -/
theorem dc_infinite_iff_wide_or_strong :
  (set_of P).infinite ↔ wide P ∨ ∃ p : ℕ, p.prime ∧ strong p P :=
  ⟨dc_wide_or_strong_of_infinite h, λ h0, h0.elim infinite_pred_of_wide $
    λ h1, exists.elim h1 $ λ p h2, infinite_pred_of_strong h2.1.two_le h2.2⟩

end results

end extra
end IMOSL
