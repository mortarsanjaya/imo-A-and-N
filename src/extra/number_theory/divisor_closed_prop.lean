import data.nat.factorization.basic

/-!
# Divisor-closed proposition

We say that a `Prop`-valued map `P : ℕ → Prop` is divisor-closed if for any positive
  integer `n` for which `P(n)` holds, we also have `P(d)` for any factor `d` of `n`. 
We also define the following terminologies; most of their purposes are in number theory problems.
* We say that `P` is *wide* if `P(p)` holds for infinitely many primes `p`.
* We say that `P` is *`p`-strong* for some `p : ℕ` if `P(p^k)` holds for any `k ≥ 0`.
We defined `p`-strong generally to avoid complications.
However, its main usage comes when `p` is prime.

The main result we will prove is that `P(n)` holds for infinitely many positive integers `n`
  if and only if `P` is either wide or `p`-strong for some prime `p`.
Note that we need axiom of choice to prove this result.
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

variables {P : ℕ → Prop} [decidable_pred P] (h : divisor_closed P)
include h

/-- If `P(n)` holds for some `n ≠ 0`, then `P(1)` holds; this is obvious. -/
lemma dc_at_one {n : ℕ} (h0 : n ≠ 0) (h1 : P n) : P 1 :=
  h n h0 h1 1 (one_dvd n)

/-- An if-and-only-if criterion for a divisor-closed `Prop` map to be `p`-strong; `p ≠ 0`. -/
theorem dc_not_strong_iff {p : ℕ} (h0 : p ≠ 0) :
  ¬strong p P ↔ (∃ c : ℕ, ∀ k : ℕ, P (p ^ k) ↔ k < c) :=
begin
  simp only [strong, not_exists, not_forall],
  refine ⟨λ h1, ⟨nat.find h1, (λ k, ⟨λ h2, _, λ h2, _⟩)⟩, λ h1, _⟩,
  { rw ← not_le; intros h3,
    exact nat.find_spec h1 (h _ (pow_ne_zero k h0) h2 _ (pow_dvd_pow _ h3)) },
  { have h3 := nat.find_min h1 h2,
    rwa not_not at h3 },
  { cases h1 with c h1,
    use c; rw h1,
    exact lt_irrefl c }
end

/-- Using choice, given a `Prop` map `P` that is not `p`-strong for any `p` prime, construct a
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
  contrapose! h2; rw dif_neg h2,
  rw [dif_pos hp, ← h1, subtype.coe_mk]
end

/-- Using choice, given a `Prop` map `P` that is not `p`-strong for any `p` prime, construct a
  map `x : nat.primes → ℕ` such that `P(p^k) → k ≤ x_p` for any `k : ℕ` and `p` prime.
This is just a weak version of `dc_not_strong_aoc_map_iff`. -/
theorem dc_not_strong_aoc_map (h0 : ∀ p : ℕ, p.prime → ¬strong p P) :
  ∃ x : ℕ → ℕ, (∀ p : ℕ, x p ≠ 0 → p.prime) ∧
    ∀ (p : ℕ) (hp : p.prime) (k : ℕ), P (p ^ k) → k ≤ x p :=
begin
  rcases dc_not_strong_aoc_map_iff h h0 with ⟨x, h1, h2⟩,
  exact ⟨x, h1, λ p hp k h3, le_of_lt ((h2 p hp k).mp h3)⟩
end

/-- Using choice, given a `Prop` map `P` that is not `p`-strong for any `p` prime, under the
  condition `P(1)`, construct a map `x : nat.primes → ℕ` such that `P(p^k) ↔ k ≤ x_p` for any
  `k : ℕ` and `p` prime. -/
theorem dc_not_strong_aoc_map_iff' (h0 : ∀ p : ℕ, p.prime → ¬strong p P) (h1 : P 1) :
  ∃ x : ℕ → ℕ, (∀ p : ℕ, x p ≠ 0 → p.prime) ∧
    ∀ (p : ℕ) (hp : p.prime) (k : ℕ), P (p ^ k) ↔ k ≤ x p :=
begin
  rcases dc_not_strong_aoc_map_iff h h0 with ⟨x, h2, h3⟩,
  refine ⟨λ p, x p - 1, λ p h4, h2 p (λ h5, _), λ p hp k, _⟩,
  rw [h5, zero_tsub] at h4; exact h4 rfl,
  rw [h3 p hp, ← nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel],
  rwa [nat.succ_le_iff, ← h3 p hp, pow_zero]
end

/-- Using choice, given a `Prop` map `P` that is neither wide nor `p`-strong for any `p` prime,
  under the condition `P(1)`, construct a finitely-supported map `x : nat.primes → ℕ` such that
  `P(p^k) ↔ k ≤ x_p` for any `k : ℕ` and `p` prime. -/
theorem dc_not_wide_strong_aoc_finsupp
    (h0 : ¬wide P) (h1 : ∀ p : ℕ, p.prime → ¬strong p P) (h2 : P 1) :
  ∃ x : ℕ →₀ ℕ, (∀ p : ℕ, x p ≠ 0 → p.prime) ∧
    ∀ (p : ℕ) (hp : p.prime) (k : ℕ), P (p ^ k) ↔ k ≤ x p :=
begin
  simp only [wide, set.not_infinite] at h0,
  replace h2 := dc_not_strong_aoc_map_iff' h h1 h2,
  clear h h1; rcases h2 with ⟨x, h, h1⟩,
  refine ⟨⟨h0.to_finset, x, (λ p, _)⟩, ⟨h, h1⟩⟩,
  rw [set.finite.mem_to_finset, set.mem_set_of_eq, iff.comm],
  refine ⟨λ h2, ⟨h p h2, _⟩, λ h2, _⟩,
  rwa [← pow_one p, h1 p (h p h2), nat.succ_le_iff, zero_lt_iff],
  rw [← zero_lt_iff, ← nat.succ_le_iff, ← h1 p h2.1, pow_one],
  exact h2.2
end

/-- Assuming choice, `P(n)` holds for infinitely many `n` iff
  `P` is either wide or `p`-strong for some `p` prime. -/
theorem dc_infinite_iff_wide_or_strong :
  (set_of P).infinite ↔ wide P ∨ ∃ p : ℕ, p.prime ∧ strong p P :=
begin
  refine iff.symm ⟨_, λ h0, _⟩,
  { rintros (h0 | ⟨p, hp, h0⟩),
    refine set.infinite.mono (λ x h1, _) h0; exact h1.2,
    exact set.infinite_of_injective_forall_mem (nat.pow_right_injective hp.two_le) h0 },
  by_cases h1 : ¬P 1,
  { rcases set.infinite.exists_nat_lt h0 0 with ⟨n, h2, h3⟩,
    exfalso; exact h1 (dc_at_one h (ne_of_gt h3) h2) },
  { contrapose! h0,
    rw not_not at h1,
    replace h0 := dc_not_wide_strong_aoc_finsupp h h0.1 h0.2 h1,
    clear h1; rcases h0 with ⟨x, h0, h1⟩,
    suffices : ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, P n → n = 0 ∨ n ∣ N,
    { rcases this with ⟨N, hN, this⟩,
      refine not_not.mpr (set.finite.subset (finset.range N.succ).finite_to_set (λ n h2, _)),
      rw [finset.mem_coe, finset.mem_range, nat.lt_succ_iff],
      rcases this n h2 with rfl | h2,
      exacts [N.zero_le, nat.le_of_dvd hN h2] },
    use x.prod has_pow.pow,
    rw and_iff_left_of_imp,
    { refine nat.prod_pow_pos_of_zero_not_mem_support (λ h2, _),
      rw finsupp.mem_support_iff at h2,
      exact nat.not_prime_zero (h0 0 h2) },
    { intros h2 n h3,
      rcases eq_or_ne n 0 with rfl | h4,
      left; refl,
      rw [or_iff_right h4, ← nat.factorization_le_iff_dvd h4 (ne_of_gt h2),
          nat.prod_pow_factorization_eq_self (by simp; exact h0), finsupp.le_iff],
      rintros p h5,
      replace h5 : p.prime := nat.prime_of_mem_factorization h5,
      rw [nat.factorization_def n h5, ← h1 p h5],
      exact h n h4 h3 _ pow_padic_val_nat_dvd } }
end

end results

end extra
end IMOSL
