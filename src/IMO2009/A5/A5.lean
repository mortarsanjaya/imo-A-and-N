import algebra.order.field tactic.by_contra

/-! # IMO 2009 A5 -/

namespace IMOSL
namespace IMO2009A5

theorem final_solution {F : Type*} [linear_ordered_field F] (f : F → F) :
  ∃ x y : F, y * f x + x < f (x - f y) :=
begin

  ---- Assume contradiction, and start with `f(t) ≤ t + f(0)` for all `t : F`
  by_contra' h,
  have h0 : ∀ t : F, f t ≤ t + f 0 :=
  begin
    intros t,
    replace h := h (t + f 0) 0,
    rwa [add_sub_cancel, zero_mul, zero_add] at h
  end,
  by_cases h1 : ∀ x : F, f x ≤ 0,

  ---- Case 1: `f(x) ≤ 0` for all `x : F`
  { replace h0 : ∀ t : F, f t ≤ t :=
      λ t, le_trans (h0 t) (add_le_of_nonpos_right (h1 0)),
    cases exists_gt (max 0 (- 1 - f (-1))) with t h2,
    rw max_lt_iff at h2; cases h2 with h2 h3,
    revert h3; rw [imp_false, not_lt, le_sub_iff_add_le, ← le_sub_iff_add_le', ← neg_add'],
    replace h := h (f t - 1) t,
    rw sub_sub_cancel_left at h,
    refine le_trans h _; clear h,
    rw ← le_sub_iff_add_le,
    refine le_trans ((mul_le_mul_left h2).mpr (h0 _)) _,
    rw [le_sub_iff_add_le, ← add_one_mul, add_comm,
        le_neg_iff_add_nonpos_right, ← mul_add_one, sub_add_cancel],
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (add_pos one_pos h2)) (h1 t) },

  ---- Case 2: `f(c) > 0` for some `c : F`
  { simp only [not_forall, not_le] at h1,
    cases h1 with c h1,
    cases exists_lt (min (c - f 0) ((- 1 - c - f 0) / f c)) with t h2,
    rw lt_min_iff at h2; cases h2 with h2 h3,
    rw [lt_div_iff h1, sub_right_comm, lt_sub_iff_add_lt] at h3,
    revert h3; clear h1; rw [imp_false, not_lt],
    refine le_trans _ (h c t),
    rw sub_le_iff_le_add; refine le_trans _ (h0 _),
    rw lt_sub_iff_add_lt at h2,
    replace h2 := lt_of_le_of_lt (h0 t) h2,
    rw ← sub_pos at h2,
    generalize_hyp : c - f t = y at h2 ⊢,

    -- Remains to prove `f(f(y)) ≥ -1` for all `y > 0`
    replace h := le_trans (h (f y) y) (add_le_add_left (h0 y) _),
    rw [sub_self, ← add_assoc, le_add_iff_nonneg_left, ← mul_add_one] at h,
    rwa [neg_le_iff_add_nonneg, ← zero_le_mul_left h2] }

end

end IMO2009A5
end IMOSL
