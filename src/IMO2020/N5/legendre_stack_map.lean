import IMO2020.N5.additive_map number_theory.legendre_symbol.jacobi_symbol

/-!
# "Legendre stack" maps

Let `p : ℕ → ℕ := p_0 < p_1 < p_2 < ...` be an ascending chain of primes.
We call it a **Legendre stack** if `p_{n + 1} ≡ p_n (mod 4(p_n - 1)!)` for all `n ≥ 0`.
We prove some important properties related to the Legendre stack:
* For any `m : ℤ` and `j k : ℕ` with `|m| < min{p_j, p_k}`, we have `(m | p_j) = (m | p_k)`,
* For any `m n : ℕ`, `(m | p_m) (n | p_n) = (mn | p_{mn})`.
Here, `(a | b)` denotes the Jacobi/Legendre symbol.

Now, let `p` be a Legendre stack.
Let `M` be an additive monoid and `c` be a 2-torsion element of `M`.
The **Legendre stack map associated with `p` and `c`** is the map `φ` given by
  `φ(n) = c` if `(n | p_n) = -1` and `φ(n) = 0` otherwise.
We construct it as an additive map; it turns out that this map is additive.
-/

namespace IMOSL
namespace IMO2020N5

open zmod
open_locale number_theory_symbols



structure legendre_stack :=
(prime_chain : ℕ → ℕ)
(is_prime : ∀ n : ℕ, (prime_chain n).prime)
(ascending : strict_mono prime_chain)
(stacking : ∀ n : ℕ, prime_chain n.succ ≡ prime_chain n [MOD 4 * (prime_chain n).pred.factorial])



namespace legendre_stack

instance : has_coe_to_fun legendre_stack (λ _, ℕ → ℕ) := ⟨legendre_stack.prime_chain⟩

variable (p : legendre_stack)

/-- A raw bound: `n < p_n` for any `n : ℕ`. -/
lemma self_lt : ∀ n : ℕ, n < p n :=
  λ n, nat.rec_on n (p.is_prime 0).pos
    (λ n h, lt_of_le_of_lt (nat.succ_le_iff.mpr h) (p.ascending n.lt_succ_self))

/-- Equivalence of primes in the chain modulo `4`. -/
lemma eq_mod_four (k m : ℕ) : p k ≡ p m [MOD 4] :=
begin
  wlog : k ≤ m,
  refine nat.le_induction rfl (λ n _ h, h.trans _) m case,
  exact (nat.modeq.of_modeq_mul_right _ (p.stacking n)).symm
end

/-- Each prime in the chain must be odd. -/
lemma odd (n : ℕ) : odd (p n) :=
begin
  have h := p.eq_mod_four n 2,
  rw [bit0, ← two_mul] at h,
  replace h := nat.modeq.of_modeq_mul_right _ h,
  rw nat.modeq at h,
  rw [nat.odd_iff, h],
  exact (or_iff_right (ne_of_gt (p.self_lt 2))).mp (p.is_prime 2).eq_two_or_odd
end

/-- Stronger modular equivalence; for any `k ≤ m`, `p_m ≡ p_k (mod 4(p_k - 1)!). -/
lemma eq_mod_factorial {k m : ℕ} (h : k ≤ m) : p m ≡ p k [MOD 4 * (p k).pred.factorial] :=
begin
  refine nat.le_induction rfl (λ n h0 h1, nat.modeq.trans _ h1) _ h,
  obtain ⟨c, h2⟩ : (p k).pred.factorial ∣ (p n).pred.factorial :=
    nat.factorial_dvd_factorial (nat.pred_le_pred (p.ascending.monotone h0)),
  refine nat.modeq.of_modeq_mul_right c _,
  rw [mul_assoc, ← h2],
  exact p.stacking n
end

/-- For any `b : ℤ` and `k m : ℕ` with `|b| < min{p_k, p_m}`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_invariant {b : ℤ} {k m : ℕ} (hk : b.nat_abs < p k) (hm : b.nat_abs < p m) :
  J(b | p k) = J(b | p m) :=
begin
  wlog : k ≤ m,
  sorry
end

end legendre_stack





end IMO2020N5
end IMOSL
