import data.nat.basic

/-!
# AM-GM-style induction

Let `P : ℕ → Prop` be an `ℕ`-predicate.
Suppose that we have `P(1)`, `P(n) → P(2n)`, and `P(n + 1) → P(n)` for any `n : ℕ`.
Then `P(n)` holds for all `n : ℕ`.
This file provides a proof of this statement.
We also prove a multiset version of the statement.
-/

namespace IMOSL
namespace extra

/-- `ℕ`-based AM-GM induction -/
theorem AM_GM_induction {P : ℕ → Prop} (h : P 1)
  (h0 : ∀ n : ℕ, P n → P (2 * n)) (h1 : ∀ n : ℕ, P n.succ → P n) : ∀ n : ℕ, P n
| 0 := h1 0 h
| 1 := h
| (n+2) := nat.decreasing_induction h1 (nat.add_le_add_right (le_of_eq_of_le n.one_mul.symm $
    nat.mul_le_mul_right n $ nat.succ_pos 1) 2) (h0 n.succ $ AM_GM_induction n.succ)

end extra
end IMOSL
