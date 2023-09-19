import extra.AM_GM_induction.multiset_AM_GM algebra.group_power.lemmas tactic.nth_rewrite

/-! # IMO 2014 C2 -/

namespace IMOSL
namespace IMO2014C2

def good {α : Type*} [has_add α] (S T : multiset α) :=
  ∃ (U : multiset α) (a b : α), S = U + {a, b} ∧ T = U + {a + b, a + b}





open multiset

section multiset_lemmas

variables {α : Type*} [has_add α]

lemma good_card_eq {S T : multiset α} (h : good S T) : T.card = S.card :=
  by rcases h with ⟨R, a, b, rfl, rfl⟩; rw [card_add, card_add, card_pair, card_pair]

lemma good_chain_card_eq : ∀ {C : list (multiset α)} {S : multiset α},
  list.chain good S C → ((list.cons S C).last (list.cons_ne_nil S C)).card = S.card
| list.nil := λ S _, congr_arg card rfl
| (T :: C) := λ S h, let h0 := list.chain_cons.mp h in
    (good_chain_card_eq h0.2).trans $ good_card_eq h0.1

end multiset_lemmas





variables {R : Type*} [linear_ordered_comm_ring R]

lemma good_nonneg {S T : multiset R} (h : good S T)
  (h0 : ∀ x : R, x ∈ S → 0 ≤ x) (x : R) (h1 : x ∈ T) : 0 ≤ x :=
begin
  rcases h with ⟨U, a, b, rfl, rfl⟩,
  rw [mem_add, insert_eq_cons, mem_cons, mem_singleton, or_self] at h1,
  refine h1.elim (λ h2, h0 x $ mem_add.mpr $ or.inl h2) (λ h2, le_of_le_of_eq _ h2.symm),
  replace h0 : ∀ x : R, x ∈ {a, b} → 0 ≤ x := λ x h3, h0 x $ mem_add.mpr $ or.inr h3,
  exact add_nonneg (h0 a $ mem_cons_self a {b}) (h0 b $ mem_cons_of_mem $ mem_singleton_self b)
end

lemma good_chain_nonneg : ∀ {C : list (multiset R)} {S : multiset R},
  (∀ x : R, x ∈ S → 0 ≤ x) → list.chain good S C →
    ∀ x : R, x ∈ (list.cons S C).last (list.cons_ne_nil S C) → 0 ≤ x
| list.nil := λ S h _, h
| (T :: C) := λ S h h0, let h1 := list.chain_cons.mp h0 in
    good_chain_nonneg (good_nonneg h1.1 h) h1.2

lemma good_prod_le {S T : multiset R} (h : good S T)
  (h0 : ∀ x : R, x ∈ S → 0 ≤ x) : (2 * 2) * S.prod ≤ T.prod :=
begin
  rcases h with ⟨U, a, b, rfl, rfl⟩,
  rw [prod_add, prod_pair, prod_add, prod_pair, mul_left_comm],
  refine mul_le_mul_of_nonneg_left _ (prod_nonneg $ λ x h, h0 x $ mem_add.mpr $ or.inl h),
  rw [← sq (a + b), add_sq', mul_assoc, two_mul, ← mul_assoc, add_le_add_iff_right],
  exact two_mul_le_add_sq a b
end

lemma good_chain_prod_le : ∀ {C : list (multiset R)} {S : multiset R},
  (∀ x : R, x ∈ S → 0 ≤ x) → list.chain good S C →
  (2 * 2) ^ C.length * S.prod ≤ ((list.cons S C).last (list.cons_ne_nil S C)).prod
| list.nil := λ S _ _, le_of_eq $ (congr_arg (* S.prod) (pow_zero _)).trans $ one_mul S.prod
| (T :: C) := λ S h h0, by rw list.chain_cons at h0; rw [list.length_cons, pow_succ', mul_assoc];
    exact (mul_le_mul_of_nonneg_left (good_prod_le h0.1 h) $
      pow_nonneg (mul_self_nonneg _) _).trans (good_chain_prod_le (good_nonneg h0.1 h) h0.2)

/-- A generalized form of the final solution -/
lemma good_chain_le_sum {C : list (multiset R)} {S : multiset R}
  (h : list.chain good S C) (h0 : ∀ x : R, x ∈ S → 0 ≤ x) :
  (S.card : R) ^ S.card * ((2 * 2) ^ C.length * S.prod)
    ≤ ((list.cons S C).last (list.cons_ne_nil S C)).sum ^ S.card :=
  (mul_le_mul_of_nonneg_left (good_chain_prod_le h0 h) $ pow_nonneg S.card.cast_nonneg _).trans $
    by rw ← good_chain_card_eq h; exact extra.multiset_AM_GM (good_chain_nonneg h0 h)





/-- Final solution -/
theorem final_solution {m : ℕ} (h : 0 < m) {C : list (multiset R)}
  (h0 : C.length = m * 2 ^ (m - 1)) : let S := replicate (2 ^ m) (1 : R) in
  list.chain good S C → 4 ^ m ≤ ((list.cons S C).last (list.cons_ne_nil S C)).sum :=
begin
  intros S h1,
  rw [bit0, ← two_mul],
  have h2 : ∀ x : R, x ∈ S → 0 ≤ x :=
    λ x h2, le_of_le_of_eq zero_le_one (eq_of_mem_replicate h2).symm,
  refine le_of_pow_le_pow (2 ^ m) (sum_nonneg $ good_chain_nonneg h2 h1)
    (pow_pos (nat.succ_pos 1) m) _,
  replace h2 := good_chain_le_sum h1 h2,
  rwa [h0, card_replicate, prod_replicate, one_pow, mul_one, nat.cast_pow,
      nat.cast_two, ← sq, ← pow_mul, ← pow_mul, mul_left_comm 2,
      ← pow_succ, nat.sub_add_cancel h, ← mul_pow, pow_mul] at h2
end

end IMO2014C2
end IMOSL
