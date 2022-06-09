import
  data.real.basic

/-
  IMO 2011 A6 (P3)
  Let f : ℝ → ℝ be a function such that, for all x, y ∈ ℝ,
          f(x + y) ≤ y f(x) + f(f(x))
  Prove that f(x) = 0 for all x ≤ 0.

  See https://www.imo-official.org/problems/IMO2011SL.pdf.
  We will follow the official Solution 1.
-/

namespace IMO2011A6

def fn_ineq (f : ℝ → ℝ) := ∀ x y : ℝ, f (x + y) ≤ y * f x + f (f x)



namespace solution

variable f : ℝ → ℝ
variable fineq : fn_ineq f
include fineq

lemma fn_lem1 :
  ∀ t x : ℝ, f t ≤ t * f x - x * f x + f (f x) :=
begin
  intros t x,
  have h := fineq x (t - x),
  rwa [add_sub_cancel'_right, sub_mul] at h,
end

lemma fn_lem2 :
  ∀ a b : ℝ, 0 ≤ f a * f b - b * f b + (f (f b) - f (f a)) :=
begin
  intros a b,
  have h := fn_lem1 f fineq (f a) b,
  rwa [add_sub, sub_nonneg],
end

lemma fn_lem3 :
  ∀ a b : ℝ, a * f a + b * f b ≤ 2 * f a * f b :=
begin
  intros a b,
  have h := add_nonneg (fn_lem2 f fineq a b) (fn_lem2 f fineq b a),
  rw [add_add_add_comm, sub_add_sub_comm, mul_comm (f b) (f a), add_sub,
      sub_add_cancel, sub_self, add_zero, sub_nonneg, add_comm] at h,
  calc a * f a + b * f b ≤ f a * f b + f a * f b : by exact h
  ... = 1 * (f a * f b) + 1 * (f a * f b) : by rw one_mul
  ... = (1 + 1) * (f a * f b) : by rw ← add_mul
  ... = (1 + 1) * f a * f b : by rw mul_assoc
  ... = 2 * f a * f b : by refl,
end

lemma fn_lem4 :
  ∀ x : ℝ, x < 0 → 0 ≤ f x :=
begin
  intros x h,
  have h0 := fn_lem3 f fineq x (2 * f x),
  rwa [add_le_iff_nonpos_left, ← div_le_iff_of_neg' h, zero_div] at h0,
end

lemma fn_lem5 :
  ∀ x : ℝ, f x ≤ 0 :=
begin
  intros x,
  rw ← not_lt; intros h,
  suffices : (∃ M : ℝ, ∀ t : ℝ, t < M → f t < 0),
  { cases this with M h0,
    let c := min M 0 - 1,
    have h1 : 0 ≤ f c,
    { apply fn_lem4 f fineq,
      rw sub_lt_zero,
      exact lt_of_le_of_lt (min_le_right M 0) zero_lt_one, },
    rw ← not_lt at h1,
    apply h1,
    apply h0,
    rw sub_lt_iff_lt_add,
    apply lt_of_le_of_lt (min_le_left M 0),
    rw lt_add_iff_pos_right,
    exact zero_lt_one, },
  use x - f (f x) / f x,
  intros t h0,
  apply lt_of_le_of_lt (fn_lem1 f fineq t x),
  rwa [← sub_mul, ← lt_neg_iff_add_neg, ← lt_div_iff h,
       sub_lt_iff_lt_add', neg_div, ← sub_eq_add_neg],
end

lemma fn_lem6 :
  ∀ x : ℝ, x < 0 → f x = 0 :=
begin
  intros x h,
  exact le_antisymm (fn_lem5 f fineq x) (fn_lem4 f fineq x h),
end

lemma fn_lem7 :
  f 0 = 0 :=
begin
  apply le_antisymm (fn_lem5 f fineq 0),
  have h := fn_lem1 f fineq (-1) (-1),
  rwa [fn_lem6 f fineq (-1), mul_zero, sub_self, zero_add] at h,
  exact neg_one_lt_zero,
end



---- Wrapper
theorem IMO2011A6_sol :
  ∀ x : ℝ, x ≤ 0 → f x = 0 :=
begin
  intros x h,
  rw le_iff_lt_or_eq at h,
  cases h with h h,
  exact fn_lem6 f fineq x h,
  rw [h, fn_lem7 f fineq],
end



end solution



end IMO2011A6
