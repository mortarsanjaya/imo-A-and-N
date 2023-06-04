import algebra.big_operators.multiset.basic extra.AM_GM_induction algebra.group_power.lemmas

/-! # IMO 2014 C2 -/

namespace IMOSL
namespace IMO2014C2

def good {α : Type*} [has_add α] (S T : multiset α) :=
  ∃ (U : multiset α) (a b : α), S = U + {a, b} ∧ T = U + {a + b, a + b}



section cons_last

variable {α : Type*} 

/-- Wrapper for the last element of a cons list `a :: l`, guaranteed to be non-empty. -/
private def cons_last (a : α) (l : list α) : α :=
  (list.cons a l).last (list.cons_ne_nil a l)

private lemma cons_last_nil (a : α) : cons_last a list.nil = a := rfl

private lemma cons_last_cons (a b : α) (l : list α) :
  cons_last a (b :: l) = cons_last b l := rfl

end cons_last



open multiset

section multiset_lemmas

variables {α : Type*}

private lemma exists_le_card_eq {n : ℕ} {T : multiset α} (h : n ≤ T.card) :
  ∃ U : multiset α, U ≤ T ∧ U.card = n :=
begin
  generalize_hyp h0 : T.card = m at h,
  revert h0 T; refine nat.le_induction (λ T h0, ⟨T, le_refl T, h0⟩) (λ k h0 h1 T h2, _) m h,
  rcases T.empty_or_exists_mem with h3 | ⟨a, h3⟩,
  rw [h3, card_zero] at h2; exact absurd h2 k.succ_ne_zero.symm,
  rcases exists_cons_of_mem h3 with ⟨U, rfl⟩,
  rw [card_cons, add_left_inj] at h2,
  cases h1 h2 with V h4,
  refine ⟨V, h4.1.trans (U.le_cons_self a), h4.2⟩
end

variables [has_add α]

private lemma good_card_eq {S T : multiset α} (h : good S T) : T.card = S.card :=
  by rcases h with ⟨R, a, b, rfl, rfl⟩; rw [card_add, card_add, card_pair, card_pair]

private lemma good_chain_card_eq : ∀ {C : list (multiset α)} {S : multiset α},
  list.chain good S C → (cons_last S C).card = S.card
| list.nil := λ S _, congr_arg card (cons_last_nil S)
| (T :: C) := λ S h, let h0 := list.chain_cons.mp h in
    (congr_arg card $ cons_last_cons S T C).trans $
      (good_chain_card_eq h0.2).trans $ good_card_eq h0.1

end multiset_lemmas





variables {R : Type*} [linear_ordered_comm_ring R]

/-- This takes between 0.5s and 0.7s... but I don't think it can be improved either. -/
lemma multiset_AM_GM : ∀ {S : multiset R},
  (∀ x : R, x ∈ S → 0 ≤ x) → (S.card : R) ^ S.card * S.prod ≤ S.sum ^ S.card :=
suffices ∀ (n : ℕ) {S : multiset R}, S.card = n →
  (∀ x : R, x ∈ S → 0 ≤ x) → (n : R) ^ n * S.prod ≤ S.sum ^ n,
from λ S, this S.card rfl,
extra.AM_GM_induction
  ---- `P(1)`
  (λ S h h0, exists.elim (card_eq_one.mp h) $ λ x h1,
    by rw [nat.cast_one, pow_one, one_mul, pow_one, h1, prod_singleton, sum_singleton])
  ---- `P(n) → P(2n)`
  (λ n h S h0 h1, begin
    rw two_mul at h0,
    rcases exists_le_card_eq (le_of_le_of_eq le_add_self h0.symm) with ⟨U, h2, h3⟩,
    rw multiset.le_iff_exists_add at h2,
    rcases h2 with ⟨V, rfl⟩,
    rw [card_add, h3, add_right_inj] at h0,
    rw [prod_add, sum_add, nat.cast_mul, nat.cast_two, mul_pow, pow_mul,
        pow_mul', sq (↑n ^ n), pow_mul, mul_assoc, mul_mul_mul_comm],
    have h2 : ∀ x : R, x ∈ U → 0 ≤ x := λ x h2, h1 x $ mem_add.mpr $ or.inl h2,
    replace h1 : ∀ x : R, x ∈ V → 0 ≤ x := λ x h4, h1 x $ mem_add.mpr $ or.inr h4,
    replace h0 := h h0 h1,
    replace h3 := h h3 h2,
    replace h : 0 ≤ (n : R) ^ n := pow_nonneg n.cast_nonneg n,
    refine (mul_le_mul_of_nonneg_left (mul_le_mul h3 h0 (mul_nonneg h $ prod_nonneg h1) $
      pow_nonneg (sum_nonneg h2) n) $ pow_nonneg (sq_nonneg (2 : R)) n).trans _,
    rw [sq, ← mul_pow, ← mul_pow],
    refine pow_le_pow_of_le_left (mul_nonneg (mul_self_nonneg _) $
      mul_nonneg (sum_nonneg h2) (sum_nonneg h1)) _ _,
    rw [mul_assoc, two_mul, add_sq', ← mul_assoc, add_le_add_iff_right],
    exact two_mul_le_add_sq U.sum V.sum
  end)
  ---- `P(n + 1) → P(n)`
  (λ n h S h0 h1, begin
    replace h := @h (S.sum ::ₘ S.map (λ x, (n : R) * id x)) (by rw [card_cons, card_map, h0])
      (λ x h2, (mem_cons.mp h2).elim (λ h3, le_of_le_of_eq (sum_nonneg h1) h3.symm) $
      λ h3, exists.elim (mem_map.mp h3) $
        λ c h4, le_of_le_of_eq (mul_nonneg n.cast_nonneg $ h1 c h4.1) h4.2),
    rw [prod_cons, sum_cons, sum_map_mul_left, prod_map_mul, map_id, map_const, prod_replicate,
        h0, ← one_add_mul, add_comm, ← nat.cast_succ, mul_pow, pow_succ S.sum] at h,
    refine (lt_or_eq_of_le $ sum_nonneg h1).elim (le_of_mul_le_mul_left $
      le_of_mul_le_mul_left h $ pow_pos (nat.cast_pos.mpr n.succ_pos) n.succ) (λ h2, _),
    
    replace h := all_zero_of_le_zero_le_of_sum_eq_zero h1 h2.symm,
    cases n,
    rw [pow_zero, pow_zero, one_mul, card_eq_zero.mp h0, prod_zero],
    rw [← h2, eq_replicate_card.mpr h, h0, prod_replicate, zero_pow n.succ_pos, mul_zero]
  end)

private lemma good_nonneg {S T : multiset R} (h : good S T)
  (h0 : ∀ x : R, x ∈ S → 0 ≤ x) (x : R) (h1 : x ∈ T) : 0 ≤ x :=
begin
  rcases h with ⟨U, a, b, rfl, rfl⟩,
  rw [mem_add, insert_eq_cons, mem_cons, mem_singleton, or_self] at h1,
  refine h1.elim (λ h2, h0 x $ mem_add.mpr $ or.inl h2) (λ h2, le_of_le_of_eq _ h2.symm),
  replace h0 : ∀ x : R, x ∈ {a, b} → 0 ≤ x := λ x h3, h0 x $ mem_add.mpr $ or.inr h3,
  exact add_nonneg (h0 a $ mem_cons_self a {b}) (h0 b $ mem_cons_of_mem $ mem_singleton_self b)
end

private lemma good_chain_nonneg : ∀ {C : list (multiset R)} {S : multiset R},
  (∀ x : R, x ∈ S → 0 ≤ x) → list.chain good S C → ∀ x : R, x ∈ cons_last S C → 0 ≤ x
| list.nil := λ S h _, h
| (T :: C) := λ S h h0, let h1 := list.chain_cons.mp h0 in
    good_chain_nonneg (good_nonneg h1.1 h) h1.2

private lemma good_prod_le {S T : multiset R} (h : good S T)
  (h0 : ∀ x : R, x ∈ S → 0 ≤ x) : (2 * 2) * S.prod ≤ T.prod :=
begin
  rcases h with ⟨U, a, b, rfl, rfl⟩,
  rw [prod_add, prod_pair, prod_add, prod_pair, mul_left_comm],
  refine mul_le_mul_of_nonneg_left _ (prod_nonneg $ λ x h, h0 x $ mem_add.mpr $ or.inl h),
  rw [← sq (a + b), add_sq', mul_assoc, two_mul, ← mul_assoc, add_le_add_iff_right],
  exact two_mul_le_add_sq a b
end

private lemma good_chain_prod_le : ∀ {C : list (multiset R)} {S : multiset R},
  (∀ x : R, x ∈ S → 0 ≤ x) → list.chain good S C →
  (2 * 2) ^ C.length * S.prod ≤ (cons_last S C).prod
| list.nil := λ S _ _, le_of_eq $ (congr_arg (* S.prod) (pow_zero _)).trans $ one_mul S.prod
| (T :: C) := λ S h h0, by rw list.chain_cons at h0; rw [list.length_cons, pow_succ', mul_assoc];
    exact (mul_le_mul_of_nonneg_left (good_prod_le h0.1 h) $
      pow_nonneg (mul_self_nonneg _) _).trans (good_chain_prod_le (good_nonneg h0.1 h) h0.2)

/-- A generalized form of the final solution -/
private lemma good_chain_le_sum {C : list (multiset R)} {S : multiset R}
  (h : list.chain good S C) (h0 : ∀ x : R, x ∈ S → 0 ≤ x) :
  (S.card : R) ^ S.card * ((2 * 2) ^ C.length * S.prod) ≤ (cons_last S C).sum ^ S.card :=
  (mul_le_mul_of_nonneg_left (good_chain_prod_le h0 h) $ pow_nonneg S.card.cast_nonneg _).trans $
    by rw ← good_chain_card_eq h; exact multiset_AM_GM (good_chain_nonneg h0 h)





/-- Final solution -/
theorem final_solution {m : ℕ} (h : 0 < m) {C : list (multiset R)}
  (h0 : C.length = m * 2 ^ (m - 1)) : let S := replicate (2 ^ m) (1 : R) in
  list.chain good S C → 4 ^ m ≤ (cons_last S C).sum :=
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
