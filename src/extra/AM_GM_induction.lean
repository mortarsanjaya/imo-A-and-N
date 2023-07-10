import algebra.big_operators.multiset.basic

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



section multiset

open multiset

variables {α : Type*}

/-- If `n ≤ |T|`, we can find `U ≤ T` with `|U| = n` -/
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

lemma exists_card_eq_add_eq {n : ℕ} {T : multiset α} (h : n ≤ T.card) :
  ∃ U V : multiset α, U.card = n ∧ T = U + V :=
  exists.elim (exists_le_card_eq h) $ λ U h0,
    exists.elim (multiset.le_iff_exists_add.mp h0.1) $
      λ V h1, ⟨U, V, h0.2, h1⟩

/-- `multiset α`-based AM-GM induction with raw `P(n + 1) → P(n)` hypothesis -/
theorem multiset_AM_GM_induction' {α : Type*} {P : multiset α → Prop}
  (h : ∀ a : α, P {a}) (h0 : ∀ S T : multiset α, S.card = T.card → P S → P T → P (S + T))
  (h1 : ∀ S : multiset α, (∀ T : multiset α, T.card = S.card + 1 → P T) → P S) :
  ∀ S : multiset α, P S :=
suffices ∀ (n : ℕ) {S : multiset α}, S.card = n → P S, from λ S, this S.card rfl,
AM_GM_induction
---- `P(1)`
(λ S h2, exists.elim (card_eq_one.mp h2) $ λ a h2, cast (congr_arg P h2.symm) (h a))
---- `P(n) → P(2n)`
(λ n h2 S h3, begin
  rw two_mul at h3,
  rcases exists_card_eq_add_eq (le_add_self.trans_eq h3.symm) with ⟨T, U, h4, rfl⟩,
  rw [card_add, h4, add_right_inj] at h3,
  exact h0 T U (h4.trans h3.symm) (h2 h4) (h2 h3)
end)
---- `P(n + 1) → P(n)`
(λ n h2 S h3, h1 S $ λ T h4, h2 $ h4.trans $ congr_arg nat.succ h3)

/-- `multiset α`-based AM-GM induction -/
theorem multiset_AM_GM_induction {α : Type*} {P : multiset α → Prop}
  (h : ∀ a : α, P {a}) (h0 : ∀ S T : multiset α, S.card = T.card → P S → P T → P (S + T))
  (h1 : ∀ S : multiset α, ∃ (a : α) (T : multiset α), T.card = S.card ∧ (P (a ::ₘ T) → P S)) :
  ∀ S : multiset α, P S :=
multiset_AM_GM_induction' h h0 $ λ S h2, exists.elim (h1 S) $ λ a h3,
  exists.elim h3 $ λ T h3, h3.2 $ h2 _ $ (card_cons a T).trans $ congr_arg nat.succ h3.1

end multiset

end extra
end IMOSL
