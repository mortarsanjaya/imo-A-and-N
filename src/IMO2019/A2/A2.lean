import
  algebra.order.group.min_max
  algebra.group_power.lemmas
  data.multiset.fold

/-! # IMO 2019 A2 -/

namespace IMOSL
namespace IMO2019A2

open multiset 

variables {R : Type*} [linear_ordered_comm_ring R]

section results

lemma le_fold_max_of_mem (S : multiset R) : ∀ x : R, x ∈ S → x ≤ S.fold max 0 :=
  multiset.induction_on S (λ x h, h.elim) $ λ a S h x h0,
    (le_max_iff.mpr $ (mem_cons.mp h0).imp le_of_eq (h x)).trans_eq
    (S.fold_cons_left _ _ _).symm 

lemma zero_le_fold_max (S : multiset R) : 0 ≤ S.fold max 0 :=
  multiset.induction_on S (le_refl 0) $ λ x S h, h.trans $
    (le_max_right x $ S.fold max 0).trans_eq (S.fold_cons_left max 0 x).symm

lemma fold_max_eq_of_all_le {S : multiset R} : (∀ x : R, x ∈ S → x ≤ 0) → S.fold max 0 = 0 :=
  multiset.induction_on S (λ _, rfl) $ λ x S h h0, let h0 := forall_mem_cons.mp h0 in
    (S.fold_cons_left _ _ _).trans $ (h h0.2).symm ▸ max_eq_right h0.1

lemma fold_max_map_neg_eq_neg_fold_min (S : multiset R) :
  (S.map has_neg.neg).fold max 0 = -S.fold min 0 :=
  multiset.induction_on S neg_zero.symm $ λ x S h,
    (S.map_cons has_neg.neg x).symm ▸ (S.fold_cons_left min 0 x).symm ▸
    ((S.map has_neg.neg).fold_cons_left max 0 (-x)).symm ▸ h.symm ▸ max_neg_neg _ _

variables {a : multiset R} (ha : ∀ x : R, x ∈ a → 0 ≤ x)
include ha

lemma sum_map_sq_le_sum_mul_max : (a.map $ λ c, c ^ 2).sum ≤ a.sum * a.fold max 0 :=
  (sum_map_le_sum_map _ _ $ λ x h, (sq x).trans_le $
    mul_le_mul_of_nonneg_left (le_fold_max_of_mem a x h) (ha x h)).trans_eq $
  sum_map_mul_right.trans $ congr_arg2 _ (congr_arg multiset.sum a.map_id') rfl

variables {b : multiset R} (hb : ∀ x : R, x ∈ b → 0 ≤ x) 
include hb

lemma lem1 : fold max 0 (a + map has_neg.neg b) = fold max 0 a :=
  (congr_arg2 (fold max) (max_self _).symm rfl).trans $ (fold_add _ _ _ _ _).trans $
    max_eq_left $ (fold_max_eq_of_all_le $ λ x h0, exists.elim (mem_map.mp h0) $
      λ c h0, h0.2.symm.trans_le $ neg_nonpos.mpr (hb c h0.1)).trans_le (zero_le_fold_max a)


variables (h : a.sum = b.sum)
include h

lemma lem2 : (a.map (λ c, c ^ 2)).sum ≤ b.card • (a.fold max 0 * b.fold max 0) :=
  (sum_map_sq_le_sum_mul_max ha).trans $ mul_comm (b.fold max 0) (a.fold max 0) ▸
    smul_mul_assoc b.card (b.fold max 0) (a.fold max 0) ▸ mul_le_mul_of_nonneg_right
      (h.trans_le $ b.sum_le_card_nsmul _ (le_fold_max_of_mem b)) (zero_le_fold_max a)

/-- The intermediate big result -/
theorem final_solution' : (a.map (λ c, c ^ 2)).sum + (b.map (λ c, c ^ 2)).sum
    ≤ (a.card + b.card) • (a.fold max 0 * b.fold max 0) :=
  (add_le_add (lem2 ha hb h) (lem2 hb ha h.symm)).trans_eq $ add_comm b.card a.card ▸
    mul_comm (fold max 0 a) (fold max 0 b) ▸ (add_nsmul _ _ _).symm

end results





open_locale classical

/-- Final solution -/
theorem final_solution {u : multiset R} (h : u.sum = 0) :
  u.card • (u.fold min 0 * u.fold max 0) ≤ -(u.map $ λ c, c ^ 2).sum :=
begin
  obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b : multiset R,
    (∀ x : R, x ∈ a → 0 ≤ x) ∧ (∀ x : R, x ∈ b → 0 ≤ x) ∧ a + b.map has_neg.neg = u :=
  begin
    refine ⟨u.filter (λ x, 0 ≤ x), (u.filter (λ x : R, ¬0 ≤ x)).map has_neg.neg,
      λ x h0, (mem_filter.mp h0).2, λ x h0, _, _⟩,
    rw mem_map at h0; rcases h0 with ⟨y, h0, rfl⟩,
    rw [mem_filter, not_le, ← neg_pos] at h0; exact le_of_lt h0.2,
    rw [map_map, neg_comp_neg, map_id]; exact u.filter_add_not _
  end,

  rw [sum_add, sum_map_neg, map_id', add_neg_eq_zero] at h,
  rw [card_add, card_map, multiset.map_add, map_map, le_neg, ← neg_nsmul, ← neg_mul, sum_add],
  simp only [function.comp_app, neg_sq],
  rw [mul_comm (-(fold min (0 : R) _)), lem1 ha hb, ← fold_max_map_neg_eq_neg_fold_min],
  refine (final_solution' ha hb h).trans_eq
    (congr_arg (has_smul.smul _) $ congr_arg (has_mul.mul $ fold max 0 a) _),
  rw [multiset.map_add, map_map, neg_comp_neg, map_id, add_comm, lem1 hb ha]
end

end IMO2019A2
end IMOSL
