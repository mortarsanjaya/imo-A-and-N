import data.nat.prime data.set.finite

/-!
# Dirichlet's theorem on arithmetic progressions

For any `d a : ℕ` coprime with `0 < d`, there exists
  infinitely many primes of form `kd + a` for some `k : ℕ`.
For now, we will just state a variant using `nat.mod`, thus assuming `a < d`.
However, we will not prove this theorem and leave it with a `sorry` proof.

The proofs are pretty much copied from the one given in
  the file `data/nat/prime.lean` for infinitude of primes.
-/

namespace IMOSL
namespace extra

variables {d a : ℕ} (h : a < d) (h0 : a.coprime d)
include h h0

axiom exists_infinite_primes_mod_eq (n : ℕ) : ∃ p : ℕ, n < p ∧ p.prime ∧ p % d = a

theorem not_bdd_above_set_of_primes_mod_eq : ¬bdd_above {p : ℕ | p.prime ∧ p % d = a} :=
  not_bdd_above_iff.mpr $ λ n, exists.elim (exists_infinite_primes_mod_eq h h0 n)
    (λ p h1, ⟨p, h1.2, h1.1⟩)

theorem infinite_set_of_primes_mod_eq : {p : ℕ | p.prime ∧ p % d = a}.infinite :=
  set.infinite_of_not_bdd_above (not_bdd_above_set_of_primes_mod_eq h h0)

end extra
end IMOSL
