import algebra.order.ring.defs algebra.big_operators.fin algebra.order.group.min_max

/-! # IMO 2019 A2 -/

namespace IMOSL
namespace IMO2019A2

open multiset function
open_locale classical

variables {R : Type*} [linear_ordered_comm_ring R]



section results

private lemma lem1 (a : multiset R) : ∀ x : R, x ∈ a → x ≤ a.fold max 0 :=
begin
  refine multiset.induction_on a _ _,
  intros x h; exfalso; exact h,
  clear a; intros x a h y h0,
  rw multiset.mem_cons at h0,
  rw [fold_cons_left, le_max_iff],
  rcases h0 with rfl | h0,
  left; exact le_refl y,
  right; exact h y h0
end

private lemma lem2 (a : multiset R) : 0 ≤ a.fold max 0 :=
begin
  refine multiset.induction_on a (by rw fold_zero) (λ x s h, _),
  rw [fold_cons_left, le_max_iff],
  right; exact h
end

private lemma lem3 {a : multiset R} (h : ∀ x : R, x ∈ a → x ≤ 0) : a.fold max 0 = 0 :=
begin
  revert h; refine multiset.induction_on a (λ h, by rw fold_zero) (λ x s h h0, _),
  rw [fold_cons_left, h (λ x h, h0 x (mem_cons_of_mem h)), max_eq_right_iff],
  exact h0 x (mem_cons_self x s)
end

private lemma lem4 (a : multiset R) : -a.fold min 0 = (a.map has_neg.neg).fold max 0 :=
begin
  refine multiset.induction_on a _ (λ x s h, _),
  rw [fold_zero, neg_zero, multiset.map_zero, fold_zero],
  rw [map_cons, fold_cons_left, fold_cons_left, ← h, max_neg_neg]
end

variables {a : multiset R} (ha : ∀ x : R, x ∈ a → 0 ≤ x)
include ha

private lemma lem5 : a.sum ≤ a.card * a.fold max 0 :=
  by convert sum_le_sum_map (const R (a.fold max 0)) (lem1 a);
    rw [map_const, sum_replicate, nsmul_eq_mul]

private lemma lem6 : (a.map (λ c, c ^ 2)).sum ≤ a.sum * a.fold max 0 :=
begin
  convert sum_map_le_sum_map (λ c, c ^ 2) (λ c, c * a.fold max 0) (λ x h, _),
  rw [sum_map_mul_right, map_id'],
  rw sq; exact mul_le_mul_of_nonneg_left (lem1 a x h) (ha x h)
end

variables {b : multiset R} (hb : ∀ x : R, x ∈ b → 0 ≤ x) 
include hb

private lemma lem7 : fold max 0 (a + map has_neg.neg b) = fold max 0 a :=
begin
  nth_rewrite 0 ← max_self (0 : R),
  rw [fold_add, max_eq_left_iff],
  convert lem2 a; refine lem3 (λ x h0, _),
  rw mem_map at h0; rcases h0 with ⟨c, h0, rfl⟩,
  rw neg_nonpos; exact hb c h0
end


variables (h : a.sum = b.sum)
include h

private lemma lem8 : (a.map (λ c, c ^ 2)).sum ≤ (b.card : R) * (a.fold max 0 * b.fold max 0) :=
begin
  rw [mul_comm (a.fold max 0), ← mul_assoc],
  refine le_trans (lem6 ha) (mul_le_mul_of_nonneg_right _ (lem2 a)),
  rw h; exact lem5 hb
end

/-- The intermediate big result -/
theorem final_solution' : (a.map (λ c, c ^ 2)).sum + (b.map (λ c, c ^ 2)).sum
    ≤ (a.card + b.card : R) * (a.fold max 0 * b.fold max 0) :=
  by convert add_le_add (lem8 ha hb h) (lem8 hb ha h.symm);
    rw [mul_comm (b.fold max 0), ← add_mul, add_comm]

end results



/-- Final solution -/
theorem final_solution {u : multiset R} (h : u.sum = 0) :
  (u.card : R) * (u.fold min 0 * u.fold max 0) ≤ -(u.map (λ c, c ^ 2)).sum :=
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
  rw [card_add, card_map, multiset.map_add, map_map, le_neg, ← mul_neg, ← neg_mul, nat.cast_add],
  simp_rw [comp_app, neg_sq, sum_add],
  rw [mul_comm (-(fold min (0 : R) _)), lem7 ha hb, lem4],
  convert final_solution' ha hb h using 3,
  rw [multiset.map_add, map_map, neg_comp_neg, map_id, add_comm, lem7 hb ha]
end

end IMO2019A2
end IMOSL
