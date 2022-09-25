import IMO2020.N5.additive_map.basic

/-!
# Sporadic maps

Fix a commutative additive monoid `M`.
Let `p : ℕ → nat.primes` be a strictly increasing prime-valued map.
Fix some `χ : Π i, additive (zmod (p i))ˣ →+ M`.
We say that `χ` is *compatible* if `χ i k = χ j k` for any
  `i j : ℕ` and `k : ℕ` with `k < p i` and `k < p j`. 
Given a compatible map `χ`, the *sporadic map* `sporadic_map M χ` is
  the additive map given by `k ↦ χ k.pred k` for `k ≠ 0`.
We also define the predicate `is_sporadic_map M` and prove an equivalent condition:
  an additive map is sporadic iff there exists infinitely many primes `p` such that
  `f(km % p) = f(k) + f(m)` for all `0 < k, m < p`.

While we can define `sporadic_map M p χ`, depending on the sequence `p`, and
  give a monoid structure on `sporadic_map M p`, we choose not to do this as
  the main focus is just constructing a non-zero sporadic map.

We also construct a non-zero sporadic map on `M = zmod 2`.
This requires Dirichlet's theorem on arithmetic progressions, which has not been implemented yet.
We will just state this theorem and replace the proof with `sorry`.
-/

namespace IMOSL
namespace IMO2020N5

end IMO2020N5
end IMOSL
