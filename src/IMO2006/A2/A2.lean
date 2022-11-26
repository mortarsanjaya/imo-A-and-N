import algebra.big_operators.order algebra.big_operators.ring

/-! # IMO 2006 A2 -/

namespace IMOSL
namespace IMO2006A2

open finset

/-- Final solution -/
theorem final_solution {F : Type*} [linear_ordered_field F] {a : ℕ → F} (h : a 0 = -1)
    (h0 : ∀ n : ℕ, 0 < n → (range n.succ).sum (λ i, a i / (n - i + 1)) = 0) :
  ∀ n : ℕ, 0 < n → 0 < a n :=
begin
  ---- Setup for strong induction
  intros n h1,
  rw [← nat.succ_le_iff, le_iff_exists_add'] at h1,
  rcases h1 with ⟨n, rfl⟩,
  induction n using nat.strong_induction_on with n n_ih,
  rcases n.eq_zero_or_pos with rfl | h1,

  ---- Base case
  replace h0 := h0 1 one_pos,
  rw [sum_range_succ, sum_range_one, h, neg_div, neg_add_eq_zero, nat.cast_one,
      sub_self, zero_add, div_one, nat.cast_zero, sub_zero, ← bit0] at h0,
  rw [zero_add, ← h0]; exact div_pos one_pos two_pos,

  ---- Induction step
  -- First obtain the main equality, substitute into the goal inequality, and manipulate
  replace h0 := congr_arg2 has_sub.sub
    (congr_arg (has_mul.mul (n + 2 : F)) (h0 n.succ n.succ_pos))
    (congr_arg (has_mul.mul (n + 1 : F)) (h0 n h1)),
  rw sum_range_succ at h0; norm_num at h0,
  rw [sub_eq_zero, add_comm _ (a n.succ), mul_add,
      ← eq_sub_iff_add_eq, mul_sum, mul_sum, ← sum_sub_distrib] at h0,
  conv_rhs at h0 { congr, skip, funext,
    rw [mul_div_left_comm, mul_div_left_comm _ (a x), ← mul_sub] },
  rw [sum_range_succ', nat.cast_zero, sub_zero, sub_zero] at h0,
  refine pos_of_mul_pos_right _ (add_nonneg n.cast_nonneg zero_le_two),
  rw h0; replace h0 : (n + 1 : F) / (n + 1) - (n + 2) / (n + 1 + 1) = 0 :=
  begin
    rw [div_self, add_assoc, ← bit0, div_self, sub_self],
    all_goals { refine ne_of_gt (add_pos (nat.cast_pos.mpr h1) _) },
    exacts [two_pos, one_pos]
  end,
  rw [h0, mul_zero, add_zero]; clear h0,

  -- It remains to show that each summand is positive
  refine sum_pos (λ i h0, mul_pos (n_ih i (mem_range.mp h0)) _) ⟨0, mem_range.mpr h1⟩,
  rw [sub_pos, bit0, ← add_assoc, ← add_sub_right_comm ↑n, ← nat.cast_succ],
  rw [mem_range, ← add_lt_add_iff_right 1, ← n.succ_eq_add_one, lt_iff_exists_add] at h0,
  generalize_hyp : n.succ = d at h0 ⊢,
  generalize_hyp h2 : i + 1 = c at h0 ⊢,
  clear n_ih h1 n h a,
  rcases h0 with ⟨t, h0, rfl⟩,
  replace h0 : 0 < (t : F) := by rw nat.cast_pos; exact h0,
  have h : 0 < (t : F) + 1 := add_pos h0 one_pos,
  rw [nat.cast_add, add_sub_cancel', div_add_same (ne_of_gt h0), add_assoc,
      div_add_same (ne_of_gt h), add_lt_add_iff_right, div_lt_div_iff h h0,
      mul_add_one, lt_add_iff_pos_right, nat.cast_pos, ← h2],
  exact i.succ_pos
end

end IMO2006A2
end IMOSL
