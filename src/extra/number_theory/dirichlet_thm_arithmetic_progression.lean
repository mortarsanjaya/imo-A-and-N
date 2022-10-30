import data.nat.prime

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

theorem exists_infinite_primes_mod_eq (n : ℕ) : ∃ p : ℕ, n < p ∧ p.prime ∧ p % d = a :=
  sorry

theorem not_bdd_above_set_of_primes_mod_eq : ¬bdd_above {p : ℕ | p.prime ∧ p % d = a} :=
begin
  rw not_bdd_above_iff; intros n,
  rcases exists_infinite_primes_mod_eq h h0 n with ⟨p, h1, h2⟩,
  exact ⟨p, h2, h1⟩
end

theorem infinite_set_of_primes_mod_eq : {p : ℕ | p.prime ∧ p % d = a}.infinite :=
  set.infinite_of_not_bdd_above (not_bdd_above_set_of_primes_mod_eq h h0)

end extra
end IMOSL
