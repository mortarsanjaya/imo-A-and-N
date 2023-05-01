import algebra.periodic

/-!
# Big operators on periodic sequences indexed by ℕ

Here we just prove the following result.
Let `M` be a commutative monoid and `n : ℕ`.
Let `a : ℕ → M` be an `n`-periodic sequence.
Then `∏ [i < n] a(i) = ∏ [i < n] a(i + k)` for any `k : ℕ`.
Similar results hold when `M` is a commutative additive monoid with sums.
-/

namespace IMOSL
namespace extra

open function finset

lemma periodic_prod_const {M : Type*} [comm_monoid M] {a : ℕ → M} {n : ℕ}
  (h : periodic a n) (k : ℕ) : (range n).prod (λ m, a (m + k)) = (range n).prod a :=
begin
  induction k with k k_ih,
  refl,
  conv_lhs { congr, skip, funext, rw [nat.succ_eq_one_add, ← add_assoc] },
  cases n with n n,
  refl,
  rw [prod_range_succ, add_comm, h, ← k_ih, prod_range_succ', zero_add]
end

lemma periodic_sum_const {M : Type*} [add_comm_monoid M] {a : ℕ → M} {n : ℕ}
  (h : periodic a n) (k : ℕ) : (range n).sum (λ m, a (m + k)) = (range n).sum a :=
begin
  induction k with k k_ih,
  refl,
  conv_lhs { congr, skip, funext, rw [nat.succ_eq_one_add, ← add_assoc] },
  cases n with n n,
  refl,
  rw [sum_range_succ, add_comm (n + 1), h, ← k_ih, sum_range_succ', zero_add]
end

end extra
end IMOSL
