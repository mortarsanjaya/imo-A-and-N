import algebra.big_operators.multiset.basic tactic.ring

/-! # IMO 2010 A2 -/

namespace IMOSL
namespace IMO2010A2

open multiset

section comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]

theorem special_identity (x : R) :
  4 * x ^ 3 - x ^ 4 = 6 * x ^ 2 - 4 * x + 1 - ((x - 1) ^ 2) ^ 2 :=
  by ring

theorem sum_identity (s : multiset R) :
  (s.map $ λ x : R, (x - 1) ^ 2).sum = (s.map $ λ x, x ^ 2).sum - 2 * s.sum + s.card :=
begin
  conv_lhs { congr, congr, funext, rw sub_sq },
  rw [sum_map_add, sum_map_sub],
  refine congr_arg2 has_add.add (congr_arg (has_sub.sub _) _) _,
  rw [sum_map_mul_right, mul_one, sum_map_mul_left, map_id'],
  rw [map_const, sum_replicate, one_pow, nsmul_one]
end

theorem sq_sum_le_sum_sq {α : Type*} {s : multiset α}
  {f : α → R} (h : ∀ a : α, a ∈ s → 0 ≤ f a) :
  (s.map $ λ a, f a ^ 2).sum ≤ (s.map f).sum ^ 2 :=
begin
  induction s using multiset.induction with c s h0,
  rw [multiset.map_zero, multiset.map_zero, sum_zero, zero_pow (nat.succ_pos 1)],
  rw [map_cons, map_cons, sum_cons, sum_cons, add_sq'],
  have h1 : ∀ a : α, a ∈ s → 0 ≤ f a := λ x h1, h x $ mem_cons_of_mem h1,
  exact le_add_of_le_of_nonneg (add_le_add_left (h0 h1) (f c ^ 2))
    (mul_nonneg (mul_nonneg zero_le_two $ h c $ mem_cons_self c s) $
      sum_nonneg $ λ x h2, exists.elim (mem_map.mp h2) $ λ a h3, le_of_le_of_eq (h1 a h3.1) h3.2)
end

theorem QM_AM {α : Type*} (s : multiset α) (f : α → R) :
  (s.map f).sum ^ 2 ≤ s.card • (s.map $ λ a, f a ^ 2).sum :=
begin
  induction s using multiset.induction with c s h,
  rw [card_zero, zero_nsmul, multiset.map_zero, sum_zero, zero_pow (nat.succ_pos 1)],
  rw [map_cons, map_cons, sum_cons, sum_cons, card_cons, succ_nsmul, add_sq,
      nsmul_add, ← add_assoc, add_assoc (f c ^ 2) _ (s.card • f c ^ 2)],
  refine add_le_add (add_le_add_left _ _) h,
  replace h : (s.map $ λ a, 2 * f c * f a).sum ≤ (s.map $ λ a, f c ^ 2 + f a ^ 2).sum :=
    sum_map_le_sum_map _ _ (λ a _, two_mul_le_add_sq (f c) (f a)),
  rwa [sum_map_mul_left, sum_map_add, map_const, sum_replicate, add_comm] at h
end

end comm_ring





variables {F : Type*} [linear_ordered_field F] {s : multiset F}

/-- Final solution, general version -/
theorem final_solution_general {B C S : F}
    (hB : B = 6 * (s.map $ λ x, x ^ 2).sum - 4 * s.sum + s.card)
    (hC : C = (s.map $ λ x, x ^ 2).sum - 2 * s.sum + s.card)
    (hS : S = (4 : F) * (s.map $ λ x, x ^ 3).sum - (s.map $ λ x, x ^ 4).sum) :
  B - C ^ 2 ≤ S ∧ S ≤ B - C ^ 2 / s.card :=
begin
  rw ← sum_identity at hC,
  rw [← sum_map_mul_left, ← sum_map_sub] at hS,
  conv_rhs at hS { congr, congr, funext, rw special_identity },
  rw [sum_map_sub, sum_map_add, map_const, sum_replicate, nsmul_one, sum_map_sub,
      sum_map_mul_left, sum_map_mul_left, map_id', ← hB] at hS,
  rw [hS, sub_le_sub_iff_left, sub_le_sub_iff_left, hC],
  exact ⟨sq_sum_le_sum_sq (λ (x : F) _, sq_nonneg (x - 1)),
    div_le_of_nonneg_of_le_mul s.card.cast_nonneg
      (sum_nonneg $ λ x h, exists.elim (mem_map.mp h) $ λ a h0, le_of_le_of_eq (sq_nonneg _) h0.2)
      (le_of_le_of_eq (QM_AM s _) (nsmul_eq_mul' _ _))⟩
end

/-- Final solution -/
theorem final_solution (h : s.card = 4) (h0 : s.sum = 6) (h1 : (s.map $ λ x, x ^ 2).sum = 12) :
  let S := (4 : F) * (s.map $ λ x, x ^ 3).sum - (s.map $ λ x, x ^ 4).sum in 36 ≤ S ∧ S ≤ 48 :=
begin
  have hB : (52 : F) = 6 * (s.map $ λ x, x ^ 2).sum - 4 * s.sum + s.card :=
    by rw [h0, h1, h]; norm_num,
  have hC : (4 : F) = (s.map $ λ x, x ^ 2).sum - 2 * s.sum + s.card :=
    by rw [h0, h1, h]; norm_num,
  exact (final_solution_general hB hC rfl).imp
    (le_of_eq_of_le $ by norm_num) (le_of_eq_of_le' $ by rw h; norm_num)
end

end IMO2010A2
end IMOSL
