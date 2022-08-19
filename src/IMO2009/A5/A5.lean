import algebra.order.field

/-! # IMO 2009 A5 -/

namespace IMOSL
namespace IMO2009A5

open_locale classical

variables {F : Type*} [linear_ordered_field F]



section results

variables {f : F → F} (fbad : ∀ x y : F, f (x - f y) ≤ y * f x + x)
include fbad

private lemma lem1 (y : F) : f y ≤ y + f 0 :=
begin
  replace fbad := fbad (y + f 0) 0,
  rwa [add_sub_cancel, zero_mul, zero_add] at fbad
end

private lemma lem2 (x : F) : f x ≤ 0 :=
begin
  rw ← not_lt; intros h,
  cases exists_lt (min (x - f 0) ((- f 0 - x - 1) / f x)) with y h0,
  rw lt_min_iff at h0; cases h0 with h0 h1,
  revert h1; rw [imp_false, not_lt, div_le_iff h, sub_right_comm, sub_le_iff_le_add],
  refine le_trans _ (fbad x y),
  rw [sub_eq_add_neg, add_comm, add_neg_le_iff_le_add],
  refine le_trans _ (lem1 fbad _),
  rw [← sub_pos, sub_sub, add_comm] at h0,
  replace h0 := lt_of_lt_of_le h0 ((sub_le_sub_iff_left x).mpr (lem1 fbad y)),
  set z := x - f y,
  replace fbad := le_trans (fbad (f z) z) (add_le_add_left (lem1 fbad z) _),
  rwa [sub_self, ← add_assoc, le_add_iff_nonneg_left, ← mul_add_one,
       zero_le_mul_left h0, ← neg_le_iff_add_nonneg] at fbad
end

end results



/-- Final solution -/
theorem final_solution (f : F → F) : ∃ x y : F, y * f x + x < f (x - f y) :=
begin
  by_contra fbad; simp only [not_exists, not_lt] at fbad,
  cases exists_gt (max 0 (- f (-1) - 1)) with y h,
  rw max_lt_iff at h; cases h with h h0,
  revert h0; rw [sub_lt_iff_lt_add, neg_lt, imp_false, not_lt, ← zero_sub (y + 1)],
  let x := f y - 1,
  have h0 := le_trans (lem1 fbad x) (add_le_of_nonpos_right (lem2 fbad 0)),
  calc f (-1) = f (x - f y) : by rw [sub_sub_cancel_left]
  ... ≤ y * f x + x : fbad x y
  ... ≤ y * (f y - 1) + x : add_le_add_right ((mul_le_mul_left h).mpr h0) _
  ... = (y + 1) * f y - (y + 1) : by rw [mul_sub_one, sub_add_sub_comm, add_one_mul]
  ... ≤ 0 - (y + 1) : sub_le_sub_right (mul_nonpos_of_nonneg_of_nonpos _ (lem2 fbad _)) _,
  exact le_of_lt (add_pos h one_pos)
end

end IMO2009A5
end IMOSL
