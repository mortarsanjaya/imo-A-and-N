import
  algebra.order.archimedean
  algebra.order.ring
  algebra.invertible
  algebra.group_power.order
  logic.function.iterate
  tactic.positivity

/-! # IMO 2014 A2 -/

namespace IMOSL
namespace IMO2014A2

open function
open_locale classical

section extra

variables {R : Type*} [linear_ordered_ring R]

lemma inverse_pos (x : R) [invertible x] : 0 < ⅟ x ↔ 0 < x :=
  pos_iff_pos_of_mul_pos (by rw inv_of_mul_self; exact one_pos)

lemma inverse_two_pos [invertible (2 : R)] : 0 < ⅟ (2 : R) :=
  by rw inverse_pos; exact two_pos

end extra







variables {R : Type*} [linear_ordered_comm_ring R] [archimedean R] [invertible (2 : R)]

def f (x : R) := ite (x < ⅟ 2) (x + ⅟ 2) (x ^ 2)



private lemma lem1 {x : R} (h : 0 < x ∧ x < 1) (n : ℕ) : 0 < (f^[n] x) ∧ (f^[n] x) < 1 :=
begin
  induction n with n n_ih,
  rwa iterate_zero,
  rw [iterate_succ', comp_app, f],
  cases n_ih with h0 h1,
  by_cases h2 : (f^[n] x) < (⅟ 2),
  rw if_pos h2; exact ⟨add_pos h0 (lt_trans h0 h2),
    lt_of_lt_of_eq (add_lt_add_right h2 (⅟ 2)) inv_of_two_add_inv_of_two⟩,
  rw if_neg h2; exact ⟨pow_pos h0 2, pow_lt_one (le_of_lt h0) h1 two_ne_zero⟩
end

private lemma lem2 {x y : R} (hx : x < ⅟ 2) (hy : y < ⅟ 2) : f x - f y = x - y :=
 by rw [f, if_pos hx, f, if_pos hy, add_sub_add_right_eq_sub]

private lemma lem3 {x y : R} (hx : ¬x < ⅟ 2) (hy : ¬y < ⅟ 2) :
  (1 + |x - y|) * |x - y| ≤ |f x - f y| :=
begin
  rw [f, if_neg hx, f, if_neg hy, sq_sub_sq, abs_mul],
  refine mul_le_mul_of_nonneg_right _ (abs_nonneg (x - y)),
  obtain ⟨u, rfl⟩ : ∃ u : R, x = u + ⅟ 2 := ⟨x - ⅟ 2, by rw sub_add_cancel⟩,
  obtain ⟨v, rfl⟩ : ∃ v : R, y = v + ⅟ 2 := ⟨y - ⅟ 2, by rw sub_add_cancel⟩,
  rw [not_lt, le_add_iff_nonneg_left] at hx hy,
  have h := add_nonneg (add_nonneg hx hy) zero_le_one,
  rw [add_add_add_comm, inv_of_two_add_inv_of_two, add_sub_add_right_eq_sub,
      abs_eq_self.mpr h, add_comm, add_le_add_iff_right],
  convert abs_sub u v; rw abs_eq_self.mpr; assumption
end

private lemma lem4 {x y : R} (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (h : x < ⅟ 2 ↔ y < ⅟ 2)
  (h0 : f x < ⅟ 2 ↔ f y < ⅟ 2) : (1 + |x - y|) * |x - y| ≤ |f (f x) - f (f y)| :=
begin
  by_cases h1 : y < ⅟ 2,
  { rw ← lem2 (by rwa h) h1,
    suffices : ¬ f y < ⅟ 2,
      exact lem3 (by rwa h0) this,
    rw [f, if_pos h1, not_lt, le_add_iff_nonneg_left],
    exact le_of_lt hy.left },
  { refine le_trans (lem3 (by rwa h) h1) _,
    by_cases h2 : f y < ⅟ 2,
    rw lem2 (by rwa h0) h2,
    refine le_trans _ (lem3 (by rwa h0) h2),
    rw [one_add_mul, ← sq, le_add_iff_nonneg_right],
    exact sq_nonneg _ }
end

private lemma lem5 {x y : R} (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
  (h : ∀ n : ℕ, f^[n] x < ⅟ 2 ↔ (f^[n] y) < ⅟ 2) : x = y :=
begin
  refine eq_of_abs_sub_eq_zero (eq_of_ge_of_not_gt (abs_nonneg _) (λ h0, _)),
  replace h : ∀ n : ℕ, (1 + |x - y|) ^ n * |x - y| ≤ |(f^[2 * n] x) - (f^[2 * n] y)| :=
  begin
    intros n; induction n with n n_ih,
    rw [pow_zero, one_mul, mul_zero, iterate_zero, id_def],
    rw [nat.mul_succ, add_comm _ 2, iterate_add, comp_app, iterate_succ,
        iterate_one, comp_app, comp_app, comp_app, pow_succ, mul_assoc],
    refine le_trans _ (lem4 (lem1 hx _) (lem1 hy _) (h _) _),
    work_on_goal 2 { convert (h (2 * n + 1)); rw iterate_succ' },
    refine mul_le_mul _ n_ih _ _; try { positivity },
    rw add_le_add_iff_left; refine le_trans _ n_ih,
    rw [← sub_nonneg, ← sub_one_mul],
    refine mul_nonneg _ (abs_nonneg _),
    rw sub_nonneg; refine one_le_pow_of_one_le _ n,
    rw le_add_iff_nonneg_right; exact abs_nonneg _
  end,

  obtain ⟨N, h1⟩ : ∃ N : ℕ, 1 < (1 + |x - y|) ^ N * |x - y| :=
  begin
    cases archimedean.arch 1 h0 with c h1,
    rw nsmul_eq_mul at h1,
    cases add_one_pow_unbounded_of_pos (c : R) h0 with N h2,
    rw add_comm at h2,
    exact ⟨N, lt_of_le_of_lt h1 ((mul_lt_mul_right h0).mpr h2)⟩
  end,

  replace h1 := lt_of_lt_of_le h1 (h N),
  replace hx := lem1 hx (2 * N),
  replace hy := lem1 hy (2 * N),
  revert h1; refine lt_asymm _,
  rw abs_sub_lt_iff; split,
  convert sub_lt_sub hx.right hy.left; rw sub_zero,
  convert sub_lt_sub hy.right hx.left; rw sub_zero
end

private lemma lem6 {x : R} (h : f x = x) : x = 1 :=
begin
  by_cases h0 : x < ⅟ 2,
  rw [f, if_pos h0, add_right_eq_self] at h,
  exfalso; exact ne_of_gt inverse_two_pos h,
  rw [f, if_neg h0, sq, ← sub_eq_zero, ← mul_sub_one, mul_eq_zero, sub_eq_zero] at h,
  rcases h with rfl | rfl,
  exfalso; exact h0 inverse_two_pos,
  refl
end

private lemma lem7 {x : R} (h : x < 1) : x < f x ↔ x < ⅟ 2 :=
begin
  by_cases h0 : x < ⅟ 2,
  simp only [f, h0, if_true, iff_true, lt_add_iff_pos_right],
  exact inverse_two_pos,
  simp only [f, h0, if_false, iff_false, sq, not_lt],
  rw [← sub_nonneg, ← one_sub_mul],
  refine mul_nonneg _ _,
  rw sub_nonneg; exact le_of_lt h,
  rw not_lt at h0; exact le_trans (le_of_lt inverse_two_pos) h0
end



/- Final solution -/
theorem final_solution {x y : R} (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
  (h : ∀ n : ℕ, 0 ≤ (f^[n + 1] x - (f^[n] x)) * (f^[n + 1] y - (f^[n] y))) : x = y :=
begin
  refine lem5 hx hy _; intros n,
  rw [← lem7 (lem1 hx n).right, ← lem7 (lem1 hy n).right],
  replace h := eq_or_lt_of_le (h n),
  rw [iterate_succ', comp_app, comp_app, zero_eq_mul, sub_eq_zero, sub_eq_zero] at h,
  rcases h with (h | h) | h,
  exfalso; exact ne_of_lt (lem1 hx n).right (lem6 h),
  exfalso; exact ne_of_lt (lem1 hy n).right (lem6 h),
  replace h := pos_iff_pos_of_mul_pos h,
  rwa [sub_pos, sub_pos] at h
end

end IMO2014A2
end IMOSL
