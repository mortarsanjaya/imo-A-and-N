import
  extra.AM_GM_induction.basic
  algebra.big_operators.multiset.basic
  data.nat.cast.basic
  tactic.nth_rewrite

/-!
# Multiset AM-GM on rings

We provide the general AM-GM induction framework for multisets.
We also prove the unweighted version of AM-GM on rings.
-/

namespace IMOSL
namespace extra

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

/-- If `n ≤ |T|`, we can find `U, V` with `|U| = n` and `T = U + V` -/
lemma exists_card_eq_add_eq {n : ℕ} {T : multiset α} (h : n ≤ T.card) :
  ∃ U V : multiset α, U.card = n ∧ T = U + V :=
  exists.elim (exists_le_card_eq h) $ λ U h0,
    exists.elim (multiset.le_iff_exists_add.mp h0.1) $
      λ V h1, ⟨U, V, h0.2, h1⟩

/-- `multiset α`-based AM-GM induction with raw `P(n + 1) → P(n)` hypothesis -/
theorem multiset_AM_GM_induction {α : Type*} {P : multiset α → Prop}
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



/-- This takes between 0.5s and 0.7s... but I don't think it can be improved either. -/
lemma multiset_AM_GM {R : Type*} [linear_ordered_comm_ring R] :
  ∀ {S : multiset R}, (∀ x : R, x ∈ S → 0 ≤ x) →
  (S.card : R) ^ S.card * S.prod ≤ S.sum ^ S.card :=
extra.multiset_AM_GM_induction
---- `P({a})`
(λ a h, by rw [card_singleton, nat.cast_one, one_pow,
  one_mul, prod_singleton, sum_singleton, pow_one])
---- `|S| = |T| → P(S) → P(T) → P(S + T)`
(λ S T h h0 h1 h2, begin
  rw ← h at h1,
  rw [card_add, prod_add, sum_add, ← h, ← two_mul, nat.cast_mul, nat.cast_two, mul_pow,
      pow_mul, pow_mul', sq (↑S.card ^ _), pow_mul, mul_assoc, mul_mul_mul_comm],
  have h3 : ∀ x : R, x ∈ S → 0 ≤ x := λ x h3, h2 x $ mem_add.mpr $ or.inl h3,
  replace h2 : ∀ x : R, x ∈ T → 0 ≤ x := λ x h4, h2 x $ mem_add.mpr $ or.inr h4,
  have h4 : 0 ≤ (S.card : R) ^ S.card := pow_nonneg S.card.cast_nonneg S.card,
  refine (mul_le_mul_of_nonneg_left
    (mul_le_mul (h0 h3) (h1 h2) (mul_nonneg h4 $ prod_nonneg h2) $
      pow_nonneg (sum_nonneg h3) S.card)
    (pow_nonneg (sq_nonneg (2 : R)) _)).trans _,
  rw [sq, ← mul_pow, ← mul_pow],
  refine pow_le_pow_of_le_left (mul_nonneg (mul_self_nonneg _) $
    mul_nonneg (sum_nonneg h3) (sum_nonneg h2)) _ _,
  rw [mul_assoc, two_mul, add_sq', ← mul_assoc, add_le_add_iff_right],
  exact two_mul_le_add_sq S.sum T.sum
end)
---- `P(a ::ₘ T) → P(S)` for some `a : R` and `T : multiset R`
(λ S h h0, (eq_or_lt_of_le $ sum_nonneg h0).elim
  -- `∑_{x ∈ S} x = 0`
  (λ h1, begin
    cases S.card.eq_zero_or_pos with h2 h2,
    rw [← h1, h2, pow_zero, pow_zero, one_mul, card_eq_zero.mp h2, prod_zero],
    nth_rewrite 2 eq_replicate_card.mpr (all_zero_of_le_zero_le_of_sum_eq_zero h0 h1.symm),
    rw [← h1, prod_replicate, zero_pow h2, mul_zero]
  end)
  -- `∑_{x ∈ S} x > 0`
  (λ h1, begin
    have h2 : 0 < ((S.card + 1 : ℕ) : R) := nat.cast_pos.mpr S.card.succ_pos,
    replace h := h (S.sum ::ₘ S.map (λ x, (S.card : R) * id x))
      ((card_cons _ _).trans $ congr_arg nat.succ $ S.card_map _),
    rw [card_cons, card_map, prod_cons, sum_cons, prod_map_mul, sum_map_mul_left,
        map_id, map_const, prod_replicate, ← one_add_mul, add_comm (1 : R),
        ← nat.cast_add_one, mul_pow, mul_le_mul_left (pow_pos h2 _), pow_succ] at h,
    refine le_of_mul_le_mul_left (h $ λ x h, _) h1,
    rw [mem_cons, mem_map] at h; rcases h with rfl | ⟨a, h, rfl⟩,
    exacts [sum_nonneg h0, mul_nonneg (S.card.cast_nonneg) (h0 a h)]
  end))

end extra
end IMOSL
