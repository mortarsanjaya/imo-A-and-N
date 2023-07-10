import algebra.big_operators.multiset.basic

/-!
# AM-GM-style induction

Let `P : ℕ → Prop` be an `ℕ`-predicate.
Suppose that we have `P(1)`, `P(n) → P(2n)`, and `P(n + 1) → P(n)` for any `n : ℕ`.
Then `P(n)` holds for all `n : ℕ`.
This file provides a proof of this statement.

This is the standard inductive proof for unweighted AM-GM.
Hence the author decides to call it the AM-GM induction.
-/

namespace IMOSL
namespace extra

theorem AM_GM_induction {P : ℕ → Prop} (h : P 1)
  (h0 : ∀ n : ℕ, P n → P (2 * n)) (h1 : ∀ n : ℕ, P n.succ → P n) : ∀ n : ℕ, P n
| 0 := h1 0 h
| 1 := h
| (n+2) := nat.decreasing_induction h1 (nat.add_le_add_right (le_of_eq_of_le n.one_mul.symm $
    nat.mul_le_mul_right n $ nat.succ_pos 1) 2) (h0 n.succ $ AM_GM_induction n.succ)



section multiset

open multiset

variables {α : Type*}

lemma exists_le_card_eq {n : ℕ} {T : multiset α} (h : n ≤ T.card) :
  ∃ U : multiset α, U ≤ T ∧ U.card = n :=
begin
  generalize_hyp h0 : T.card = m at h,
  revert h0 T; refine nat.le_induction (λ T h0, ⟨T, le_refl T, h0⟩) (λ k h0 h1 T h2, _) m h,
  rcases T.empty_or_exists_mem with h3 | ⟨a, h3⟩,
  rw [h3, card_zero] at h2; exact absurd h2 k.succ_ne_zero.symm,
  rcases exists_cons_of_mem h3 with ⟨U, rfl⟩,
  rw [card_cons, add_left_inj] at h2,
  cases h1 h2 with V h4,
  exact ⟨V, h4.1.trans (U.le_cons_self a), h4.2⟩
end

theorem multiset_AM_GM_induction {α : Type*} [nonempty α] {P : multiset α → Prop}
  (h : ∀ a : α, P {a}) (h0 : ∀ S T : multiset α, S.card = T.card → P S → P T → P (S + T))
  (h1 : ∀ (a : α) (S : multiset α), P (a ::ₘ S) → P S) : ∀ S : multiset α, P S :=
suffices ∀ (n : ℕ) {S : multiset α}, S.card = n → P S, from λ S, this S.card rfl,
AM_GM_induction
---- `P(1)`
(λ S h2, exists.elim (card_eq_one.mp h2) $ λ a h2, cast (congr_arg P h2.symm) (h a))
---- `P(n) → P(2n)`
(λ n h2 S h3, begin
  rw two_mul at h3,
  rcases exists_le_card_eq (le_add_self.trans_eq h3.symm) with ⟨T, h4, h5⟩,
  rw multiset.le_iff_exists_add at h4,
  rcases h4 with ⟨U, rfl⟩,
  rw [card_add, h5, add_right_inj] at h3,
  exact h0 T U (h5.trans h3.symm) (h2 h5) (h2 h3)
end)
---- `P(n + 1) → P(n)`
(λ n h2 S h3, _inst_1.elim $ λ a, h1 a S $ h2 $ (S.card_cons _).trans $ congr_arg nat.succ h3)

end multiset

end extra
end IMOSL
