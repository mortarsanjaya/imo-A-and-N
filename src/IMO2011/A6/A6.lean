import data.real.basic

namespace IMOSL
namespace IMO2011A6

/--
  IMO 2011 A6 (P3)

  Let f : ℝ → ℝ be a function such that, for all x, y ∈ ℝ,
          f(x + y) ≤ y f(x) + f(f(x)).
  Prove that f(x) = 0 for all x ≤ 0.

  See https://www.imo-official.org/problems/IMO2011SL.pdf.
  We will follow the official Solution 1.
-/
def fn_ineq (f : ℝ → ℝ) := ∀ x y : ℝ, f (x + y) ≤ y * f x + f (f x)



namespace results

variables {f : ℝ → ℝ} (fineq : fn_ineq f)
include fineq

lemma fn_lem1 (t x : ℝ) : f t ≤ t * f x - x * f x + f (f x) :=
begin
  have h := fineq x (t - x),
  rwa [add_sub_cancel'_right, sub_mul] at h
end

lemma fn_lem2 (x : ℝ) (h : x < 0) : 0 ≤ f x :=
begin
  have step2 : ∀ a b : ℝ, a * f a + b * f b ≤ 2 * f a * f b :=
    λ a b, by linarith [add_le_add (fn_lem1 fineq (f b) a) (fn_lem1 fineq (f a) b)],
  have h0 := step2 x (2 * f x),
  rwa [add_le_iff_nonpos_left, ← div_le_iff_of_neg' h, zero_div] at h0
end

lemma fn_lem3 (x : ℝ) : f x ≤ 0 :=
begin
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
  exact not_lt_of_le (fn_lem2 fineq C h2) (h0 C h1)
end

end results



/-- Final solution -/
theorem final_solution {f : ℝ → ℝ} (fineq : fn_ineq f) (x : ℝ) (h : x ≤ 0) : f x = 0 :=
begin
  have step1 : ∀ x : ℝ, x < 0 → f x = 0 :=
    by intros x h; exact le_antisymm (results.fn_lem3 fineq x) (results.fn_lem2 fineq x h),
  rw le_iff_lt_or_eq at h,
  rcases h with h | rfl,
  exact step1 x h,
  cases exists_lt (0 : ℝ) with x h,
  have h0 := fineq x 0,
  rw [zero_mul, zero_add, add_zero, step1 x h] at h0,
  exact le_antisymm (results.fn_lem3 fineq 0) h0
end

end IMO2011A6
end IMOSL
