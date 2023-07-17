import algebra.big_operators.multiset.basic data.multiset.fold

/-! # IMO 2019 C2 -/

namespace IMOSL
namespace IMO2019C2

open multiset

section extra_lemmas

variables {α : Type*} [linear_order α]

lemma multiset_max_mem_cons (a : α) (S : multiset α) : S.fold max a ∈ a ::ₘ S :=
multiset.induction_on S (mem_cons_self a 0) $
λ b T h, begin
  rw [fold_cons_left, cons_swap],
  cases max_choice b (T.fold max a) with h0 h0,
  rw h0; exact mem_cons_self b (a ::ₘ T),
  rw h0; exact mem_cons_of_mem h
end

lemma multiset_le_max_of_mem (a : α) (S : multiset α) :
  ∀ b : α, b ∈ a ::ₘ S → b ≤ S.fold max a :=
multiset.induction_on S
(λ b h, by rw [cons_zero, mem_singleton] at h; exact le_of_eq h)
(λ b T h c h0, begin
  rw [fold_cons_left, le_max_iff],
  rw cons_swap at h0,
  exact (mem_cons.mp h0).imp le_of_eq (h c)
end)

lemma exists_max_add_rest {S : multiset α} (h : S ≠ 0) :
  ∃ (a : α) (S0 : multiset α), S = a ::ₘ S0 ∧ ∀ x : α, x ∈ S0 → x ≤ a :=
begin
  cases exists_mem_of_ne_zero h with b h0,
  cases exists_cons_of_mem h0 with T h1,
  cases exists_cons_of_mem (multiset_max_mem_cons b T) with U h2,
  refine ⟨T.fold max b, U, h1.trans h2, λ x h3, multiset_le_max_of_mem _ _ _ _⟩,
  rw h2; exact mem_cons_of_mem h3
end

end extra_lemmas





/-- Final solution -/
theorem final_solution {G : Type*} [linear_ordered_add_comm_group G] {g : G} (h : 0 ≤ g) :
  ∀ {S : multiset G}, (∀ x : G, x ∈ S → g ≤ x) → S.sum ≤ (2 * S.card) • g →
    ∀ r : G, -(2 • g) ≤ r → r ≤ S.sum → 
      ∃ T : multiset G, T ≤ S ∧ r ≤ T.sum ∧ T.sum ≤ r + 2 • g :=
suffices ∀ (n : ℕ) {S : multiset G}, S.card = n →
  (∀ x : G, x ∈ S → g ≤ x) → S.sum ≤ (2 * n) • g →
    ∀ r : G, -(2 • g) ≤ r → r ≤ S.sum → 
      ∃ T : multiset G, T ≤ S ∧ r ≤ T.sum ∧ T.sum ≤ r + 2 • g,
from λ S, this S.card rfl,
begin
  intros n; induction n with n n_ih,
  ---- `|S| = 0`
  { intros S h0 h1 h2 r h3 h4,
    refine ⟨0, multiset.zero_le S, _⟩,
    rw [mul_zero, zero_nsmul] at h2,
    exact ⟨h4.trans h2, neg_le_iff_add_nonneg.mp h3⟩ },
  ---- `|S| = n → |S| = n + 1`
  { intros S h0 h1 h2,
    obtain ⟨s0, S0, rfl, h3⟩ :=
      exists_max_add_rest (card_pos.mp $ n.succ_pos.trans_eq h0.symm),
    rw [card_cons, nat.succ_inj'] at h0,
    rw [sum_cons, nat.mul_succ, add_nsmul, add_comm] at h2,
    replace n_ih := n_ih h0 (λ x h4, h1 x $ mem_cons_of_mem h4) (le_of_not_lt $ λ h4, _),
    ---- First prove the side goal for the IH on `S0`: `S0.sum ≤ 2n g`
    work_on_goal 2 {
      have h5 := h4.trans_le (sum_le_card_nsmul S0 s0 h3),
      rwa [h0, mul_comm, mul_nsmul] at h5,
      exact not_lt_of_le h2 (add_lt_add h4 $ lt_of_nsmul_lt_nsmul n h5) },
    ---- Back to the main goal
    intros r h4 h5,
    cases le_total r S0.sum with h6 h6,
    -- Case 1: `r ≤ S0.sum`
    { obtain ⟨T, h7, h8⟩ := n_ih r h4 h6,
      exact ⟨T, h7.trans (le_cons_self S0 s0), h8⟩ },
    -- Case 2: `S0.sum ≤ r`
    { rw [sum_cons, ← sub_le_iff_le_add'] at h5,
      obtain ⟨T, h7, h8⟩ := n_ih (r - s0) _ h5, -- Blank to be proved later: `-2g ≤ r - s0`
      rw [sub_le_iff_le_add', ← add_sub_right_comm, le_sub_iff_add_le', ← sum_cons] at h8,
      exact ⟨s0 ::ₘ T, cons_le_cons s0 h7, h8⟩,
      -- Prove the blank: `-2g ≤ r - s0`
      rw [le_sub_iff_add_le', add_neg_le_iff_le_add, ← add_le_add_iff_left S0.sum, ← add_assoc],
      refine h2.trans (add_le_add_right _ _),
      rw [mul_nsmul, ← h0, two_nsmul],
      have h7 := card_nsmul_le_sum (λ x h4, h1 x $ mem_cons_of_mem h4),
      exact add_le_add h7 (h7.trans h6) } }
end

end IMO2019C2
end IMOSL
