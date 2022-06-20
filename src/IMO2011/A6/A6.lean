import
  data.real.basic

namespace IMO2011A6

/--
  IMO 2011 A6 (P3)

  Let f : ℝ → ℝ be a function such that, for all x, y ∈ ℝ,
          f(x + y) ≤ y f(x) + f(f(x)).
  Prove that f(x) = 0 for all x ≤ 0.

  See https://www.imo-official.org/problems/IMO2011SL.pdf.
  We will follow the official Solution 1.
-/
def fn_ineq (f : ℝ → ℝ) :=
  ∀ x y : ℝ, f (x + y) ≤ y * f x + f (f x)







namespace results



variables {f : ℝ → ℝ} (fineq : fn_ineq f)
include fineq

lemma fn_lem1 :
  ∀ t x : ℝ, f t ≤ t * f x - x * f x + f (f x) :=
begin
  intros t x,
  have h := fineq x (t - x),
  rwa [add_sub_cancel'_right, sub_mul] at h,
end

lemma fn_lem2 :
  ∀ a b : ℝ, b * f b + f (f a) ≤ f a * f b + f (f b) :=
begin
  intros a b,
  rw [add_comm, ← le_sub_iff_add_le, add_sub_right_comm],
  exact fn_lem1 fineq (f a) b,
end

lemma fn_lem3 :
  ∀ a b : ℝ, a * f a + b * f b ≤ 2 * f a * f b :=
begin
  intros a b,
  have h := add_le_add (fn_lem2 fineq b a) (fn_lem2 fineq a b),
  rwa [add_add_add_comm, add_comm (f (f b)), add_add_add_comm _ (f (f a)),
       add_le_add_iff_right, mul_comm (f b), ← two_mul, ← mul_assoc] at h,
end

lemma fn_lem4 :
  ∀ x : ℝ, x < 0 → 0 ≤ f x :=
begin
  intros x h,
  have h0 := fn_lem3 fineq x (2 * f x),
  rwa [add_le_iff_nonpos_left, ← div_le_iff_of_neg' h, zero_div] at h0,
end

lemma fn_lem5 :
  ∀ x : ℝ, f x ≤ 0 :=
begin
  intros x,
  rw ← not_lt; intros h,
  let M := x - f (f x) / f x,
  have h0 : ∀ t : ℝ, t < M → f t < 0,
  { intros t h0,
    apply lt_of_le_of_lt (fn_lem1 fineq t x),
    rwa [← sub_mul, ← lt_neg_iff_add_neg, ← lt_div_iff h,
        sub_lt_iff_lt_add', neg_div, ← sub_eq_add_neg] },
  cases exists_lt (min M 0) with C h1,
  rw lt_min_iff at h1,
  cases h1 with h1 h2,
  have h3 := h0 C h1,
  have h4 := fn_lem4 fineq C h2,
  rw ← not_lt at h4,
  exact h4 h3,
end

lemma fn_lem6 :
  ∀ x : ℝ, x < 0 → f x = 0 :=
begin
  intros x h,
  exact le_antisymm (fn_lem5 fineq x) (fn_lem4 fineq x h),
end

lemma fn_lem7 :
  0 ≤ f 0 :=
begin
  cases exists_lt (0 : ℝ) with x h,
  have h0 := results.fn_lem1 fineq x x,
  rwa [results.fn_lem6 fineq x h, mul_zero, sub_self, zero_add] at h0,
end



end results







---- Final solution
theorem final_solution {f : ℝ → ℝ} (fineq : fn_ineq f) :
  ∀ x : ℝ, x ≤ 0 → f x = 0 :=
begin
  intros x h,
  rw le_iff_lt_or_eq at h,
  cases h with h h,
  exact results.fn_lem6 fineq x h,
  rw h; exact le_antisymm (results.fn_lem5 fineq 0) (results.fn_lem7 fineq),
end

end IMO2011A6
