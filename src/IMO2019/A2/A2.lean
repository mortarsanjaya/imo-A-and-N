import
  algebra.order.ring.defs
  algebra.order.group.min_max
  algebra.group_power.lemmas 
  data.multiset.fold
  tactic.nth_rewrite

/-! # IMO 2019 A2 -/

namespace IMOSL
namespace IMO2019A2

open multiset function

variables {R : Type*} [linear_ordered_comm_ring R]



section results

private lemma lem1 (a : multiset R) : ∀ x : R, x ∈ a → x ≤ a.fold max 0 :=
begin
  refine multiset.induction_on a (λ x h, h.rec _) _,
  clear a; intros x a h y h0,
  rw multiset.mem_cons at h0,
  rw [fold_cons_left, le_max_iff],
  exact h0.imp le_of_eq (h y)
end

private lemma lem2 (a : multiset R) : 0 ≤ a.fold max 0 :=
  multiset.induction_on a (le_of_eq rfl) $ λ x s h, h.trans $
    (le_max_right x $ fold max 0 s).trans_eq (fold_cons_left max 0 x s).symm

private lemma lem3 {a : multiset R} : (∀ x : R, x ∈ a → x ≤ 0) → a.fold max 0 = 0 :=
  multiset.induction_on a (λ _, rfl) $ λ x s h h0,
    by rw [fold_cons_left, h (λ x h1, h0 x $ mem_cons_of_mem h1)];
      exact max_eq_right (h0 x $ mem_cons_self x s)

private lemma lem4 (a : multiset R) : -a.fold min 0 = (a.map has_neg.neg).fold max 0 :=
  multiset.induction_on a neg_zero $ λ x s h,
    by rw [map_cons, fold_cons_left, fold_cons_left, ← h, max_neg_neg]

variables {a : multiset R} (ha : ∀ x : R, x ∈ a → 0 ≤ x)
include ha

private lemma lem5 : a.sum ≤ a.card * a.fold max 0 :=
  (sum_le_sum_map (const R $ a.fold max 0) (lem1 a)).trans_eq $
    by rw [map_const, sum_replicate, nsmul_eq_mul]

private lemma lem6 : (a.map $ λ c, c ^ 2).sum ≤ a.sum * a.fold max 0 :=
  le_of_le_of_eq (sum_map_le_sum_map _ _ $ 
    λ x h, le_of_eq_of_le (sq x) $ mul_le_mul_of_nonneg_left (lem1 a x h) (ha x h))
  (by rw [sum_map_mul_right, map_id'])

variables {b : multiset R} (hb : ∀ x : R, x ∈ b → 0 ≤ x) 
include hb

private lemma lem7 : fold max 0 (a + map has_neg.neg b) = fold max 0 a :=
begin
  nth_rewrite 0 ← max_self (0 : R),
  rw [fold_add, max_eq_left_iff],
  refine le_of_eq_of_le (lem3 $ λ x h0, _) (lem2 a),
  rw mem_map at h0; rcases h0 with ⟨c, h0, rfl⟩,
  exact neg_nonpos.mpr (hb c h0)
end


variables (h : a.sum = b.sum)
include h

private lemma lem8 : (a.map (λ c, c ^ 2)).sum ≤ (b.card : R) * (a.fold max 0 * b.fold max 0) :=
  by rw [mul_comm (a.fold max 0), ← mul_assoc];
    exact (lem6 ha).trans (mul_le_mul_of_nonneg_right (le_of_eq_of_le h $ lem5 hb) (lem2 a))

/-- The intermediate big result -/
theorem final_solution' : (a.map (λ c, c ^ 2)).sum + (b.map (λ c, c ^ 2)).sum
    ≤ (a.card + b.card : R) * (a.fold max 0 * b.fold max 0) :=
  (add_le_add (lem8 ha hb h) (lem8 hb ha h.symm)).trans_eq $
    by rw [mul_comm (b.fold max 0), ← add_mul, add_comm]

end results





open_locale classical

/-- Final solution -/
theorem final_solution {u : multiset R} (h : u.sum = 0) :
  (u.card : R) * (u.fold min 0 * u.fold max 0) ≤ -(u.map $ λ c, c ^ 2).sum :=
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
  rw [card_add, card_map, multiset.map_add, map_map, le_neg,
      ← mul_neg, ← neg_mul, nat.cast_add, sum_add],
  conv_lhs { congr, skip, congr, simp only [comp_app, neg_sq] },
  rw [mul_comm (-(fold min (0 : R) _)), lem7 ha hb, lem4],
  refine le_of_le_of_eq (final_solution' ha hb h)
    (congr_arg (has_mul.mul _) $ congr_arg (has_mul.mul $ fold max 0 a) _),
  rw [multiset.map_add, map_map, neg_comp_neg, map_id, add_comm, lem7 hb ha]
end

end IMO2019A2
end IMOSL
