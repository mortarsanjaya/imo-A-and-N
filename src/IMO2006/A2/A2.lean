import
  algebra.order.field
  algebra.big_operators.order
  algebra.big_operators.ring
  tactic.field_simp
  tactic.ring

/-! # IMO 2006 A2 -/

namespace IMOSL
namespace IMO2006A2

open finset

variables {F : Type*} [linear_ordered_field F]

/-- Final solution -/
theorem final_solution {a : ℕ → F} (h : a 0 = -1)
  (h0 : ∀ n : ℕ, 0 < n → (range n.succ).sum (λ i, a i / (n - i + 1)) = 0)
  {n : ℕ} (h1 : 0 < n) : 0 < a n :=
begin
  rw [← nat.succ_le_iff, le_iff_exists_add'] at h1,
  rcases h1 with ⟨n, rfl⟩,
  induction n using nat.strong_induction_on with n n_ih,
  rcases n.eq_zero_or_pos with rfl | h2,
  { replace h0 := h0 1 one_pos,
    rw [sum_range_succ, sub_self, zero_add, div_one, sum_range_one, h, neg_div,
        neg_add_eq_zero, nat.cast_zero, sub_zero, nat.cast_one, ← bit0] at h0,
    rw [zero_add, ← h0]; exact div_pos one_pos two_pos },
  { have h3 := congr_arg2 has_sub.sub
      (congr_arg (has_mul.mul (n + 2 : F)) (h0 n.succ n.succ_pos))
      (congr_arg (has_mul.mul (n + 1 : F)) (h0 n h2)),
    rw [mul_zero, mul_zero, sub_zero, mul_sum, sum_range_succ, sub_self, zero_add, div_one,
        add_comm, add_sub_assoc, mul_sum, ← neg_sub, ← sum_sub_distrib, add_neg_eq_zero] at h3,
    refine pos_of_mul_pos_right _ (add_nonneg n.cast_nonneg zero_le_two),
    rw h3; clear h3,
    rw [sum_range_succ', nat.cast_zero, sub_zero, sub_zero, nat.cast_succ, add_assoc, ← bit0,
        mul_div_left_comm, div_self, mul_div_left_comm, div_self, sub_self, add_zero],
    -- The two div_selfs are left out later at the end
    refine sum_pos (λ i h3, _) ⟨0, mem_range.mpr h2⟩,
    rw [mul_div_left_comm, mul_div_left_comm _ (a _), ← mul_sub],
    refine mul_pos (n_ih i (mem_range.mp h3)) _,
    have h4 : 0 < (n - i : F) := by rwa [sub_pos, nat.cast_lt, ← mem_range],
    rw [nat.cast_succ, add_sub_add_right_eq_sub, sub_add, add_sub_cancel],
    field_simp [ne_of_gt h4, ne_of_gt (add_pos h4 one_pos)],
    refine div_pos (_) (mul_pos h4 (add_pos h4 one_pos)),
    ring_nf; rw [← nat.cast_succ, nat.cast_pos]; exact i.succ_pos,
    all_goals { refine ne_of_gt (add_pos (nat.cast_pos.mpr h2) _) },
    exacts [two_pos, one_pos] }
end

end IMO2006A2
end IMOSL
