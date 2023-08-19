import algebra.order.ring.defs algebra.big_operators.multiset.basic tactic.ring

/-! # IMO 2020 A4 (P2), General properties not reliant on `ℝ` -/

namespace IMOSL
namespace IMO2020A4

section comm_ring_identities

variables {R : Type*} [comm_ring R] (a : R)

lemma ring_id1 : 1 - (3 - 2 * a) * a = (1 - 2 * a) * (1 - a) :=
  by ring

lemma ring_id2 : 1 - (3 - 2 * a) * (a ^ 2 + (1 - a) ^ 2) = 2 * (1 - a) ^ 2 * (2 * a - 1) :=
  by ring

lemma ring_id4 (b c d : R) :
  3 * (a + (b + (c + d))) - 2 * a - (a + (2 * b + (3 * c + 4 * d))) = b - d :=
  by ring

end comm_ring_identities



/-- Very obvious statement about all-`<` implies all-`≤`... -/
lemma all_le_of_all_lt {α : Type*} [linear_order α] {S : multiset α} {a : α}
  (h : ∀ x : α, x ∈ S → a < x) {x : α} (h0 : x ∈ S) : a ≤ x :=
  (h x h0).le

/-- Another straightforward statement... -/
lemma le_of_add_multiset_sum_eq {G : Type*} [linear_ordered_add_comm_group G] 
  {S : multiset G} {a b : G} (h : ∀ x : G, x ∈ S → 0 ≤ x) (h0 : a + S.sum = b) : a ≤ b :=
  (le_add_of_nonneg_right $ multiset.sum_nonneg h).trans_eq h0

/-- Choose `2` elements from a multiset of size greater than `1`. -/
lemma exists_cons_cons_eq_of_card_gt_one {α : Type*} {S : multiset α} (h : 1 < S.card) :
  ∃ (a b : α) (T : multiset α), S = a ::ₘ b ::ₘ T :=
begin
  obtain ⟨a, h0⟩ := multiset.card_pos_iff_exists_mem.mp (nat.one_pos.trans h),
  obtain ⟨S, rfl⟩ := multiset.exists_cons_of_mem h0,
  rw [S.card_cons a, nat.succ_lt_succ_iff, multiset.card_pos_iff_exists_mem] at h,
  cases h with b h,
  obtain ⟨T, rfl⟩ := multiset.exists_cons_of_mem h,
  exact ⟨a, b, T, rfl⟩
end



section comm_ring_ineq

open multiset

variables {R : Type*} [linear_ordered_comm_ring R]

lemma two_mul_lt_three_of_le_one {a : R} (h : a ≤ 1) : 2 * a < 3 :=
  (mul_le_of_le_one_right zero_le_two h).trans_lt $ lt_add_of_pos_right (2 : R) one_pos

lemma multiset_ring_prod_map_le_prod_map {ι : Type*} (f g : ι → R) {S : multiset ι} :
  (∀ i : ι, i ∈ S → 0 ≤ f i) → (∀ i : ι, i ∈ S → f i ≤ g i) →
    (S.map f).prod ≤ (S.map g).prod :=
  multiset.induction_on S (λ _ _, le_refl 1) $ λ i S h h0 h1, by calc
((i ::ₘ S).map f).prod = (f i ::ₘ S.map f).prod : congr_arg prod (S.map_cons f i)
... = f i * (S.map f).prod : (S.map f).prod_cons (f i)
... ≤ g i * (S.map g).prod :
  let h2 : i ∈ i ::ₘ S := S.mem_cons_self i in
    mul_le_mul (h1 i h2)
      (h (λ j h3, h0 j $ mem_cons_of_mem h3) (λ j h3, h1 j $ mem_cons_of_mem h3))
      (prod_nonneg $ λ a h5, exists.elim (mem_map.mp h5) $
        λ j h5, (h0 j $ mem_cons_of_mem h5.1).trans_eq h5.2)
      ((h0 i h2).trans (h1 i h2))
... = (g i ::ₘ S.map g).prod : ((S.map g).prod_cons (g i)).symm
... = ((i ::ₘ S).map g).prod : congr_arg prod (S.map_cons g i).symm

lemma ring_ineq1 {a : R} (h : 2 * a < 1) : (3 - 2 * a) * a < 1 :=
  lt_of_sub_pos $ lt_of_eq_of_lt' (ring_id1 a).symm $ mul_pos (sub_pos_of_lt h) $
    sub_pos_of_lt $ (mul_lt_mul_left zero_lt_two).mp $ h.trans $
    one_lt_two.trans_eq (mul_one 2).symm

lemma multiset_sum_sq_le_sq_sum {S : multiset R} :
  (∀ x : R, x ∈ S → 0 ≤ x) → (S.map $ λ x : R, x ^ 2).sum ≤ S.sum ^ 2 :=
multiset.induction_on S (λ _, (zero_pow $ nat.succ_pos 1).symm.le) $ λ a S h h0,
begin
  rw forall_mem_cons at h0,
  rw [map_cons, sum_cons, sum_cons, add_sq'],
  exact le_add_of_le_of_nonneg (add_le_add_left (h h0.2) _)
    (mul_nonneg (mul_nonneg zero_le_two h0.1) (sum_nonneg h0.2))
end

lemma multiset_cons_cons_sum_sq_lt_sq_sum {a b : R} (h : 0 < a) (h0 : 0 < b)
  {S : multiset R} (h1 : ∀ x : R, x ∈ S → 0 ≤ x) :
  ((a ::ₘ b ::ₘ S).map $ λ x : R, x ^ 2).sum < (a ::ₘ b ::ₘ S).sum ^ 2 :=
begin
  rw [map_cons, map_cons, sum_cons, sum_cons, sum_cons,
    sum_cons, ← add_assoc, ← add_assoc, add_sq],
  refine add_lt_add_of_lt_of_le _ (multiset_sum_sq_le_sq_sum h1),
  rw [add_sq', add_assoc],
  have X : 0 < (2 : R) := two_pos,
  exact lt_add_of_pos_right _ (add_pos_of_pos_of_nonneg (mul_pos (mul_pos X h) h0)
    (mul_nonneg (mul_nonneg X.le (add_pos h h0).le) (sum_nonneg h1)))
end

lemma multiset_sum_sq_lt_sq_sum_of_pos {S : multiset R}
  (h : 1 < S.card) (h0 : ∀ x : R, x ∈ S → 0 < x) :
  (S.map $ λ x : R, x ^ 2).sum < S.sum ^ 2 :=
begin
  rcases exists_cons_cons_eq_of_card_gt_one h with ⟨a, b, T, rfl⟩,
  rw [forall_mem_cons, forall_mem_cons] at h0,
  exact multiset_cons_cons_sum_sq_lt_sq_sum h0.1 h0.2.1 (λ x, all_le_of_all_lt h0.2.2)
end

lemma ring_ineq2 {a : R} (h : 1 ≤ 2 * a) : (3 - 2 * a) * (a ^ 2 + (1 - a) ^ 2) ≤ 1 :=
  le_of_sub_nonneg $ le_of_eq_of_le' (ring_id2 a).symm $
    mul_nonneg (mul_nonneg zero_le_two $ sq_nonneg _) (sub_nonneg_of_le h)

lemma ring_ineq3 {a : R} (h : 1 < 2 * a) (h0 : a ≠ 1) :
  (3 - 2 * a) * (a ^ 2 + (1 - a) ^ 2) < 1 :=
  lt_of_sub_pos $ lt_of_eq_of_lt' (ring_id2 a).symm $ mul_pos
    (mul_pos two_pos $ sq_pos_of_ne_zero _ $ sub_ne_zero_of_ne h0.symm) (sub_pos_of_lt h)

lemma ring_ineq4 (a b c d : R) (h : d ≤ b) :
  a + (2 * b + (3 * c + 4 * d)) ≤ 3 * (a + (b + (c + d))) - 2 * a :=
  le_of_sub_nonneg $ le_of_eq_of_le' (ring_id4 a b c d).symm $ sub_nonneg_of_le h

end comm_ring_ineq

end IMO2020A4
end IMOSL
