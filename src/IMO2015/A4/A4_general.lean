import algebra.algebra.basic

/-!
# IMO 2015 A4 (P5), Generalized Version
  
Let R be a domain.
Find all functions f : R → R such that, for all x, y ∈ R,
  f(x + f(x + y)) + f(xy) = x + f(x + y) + y f(x).

## Answer

f = id and f = x ↦ 2 - x.

## Solution

See <http://www.imo-official.org/problems/IMO2015SL.pdf>.
However, instead of working with f, we work with f - id.
That is, we will solve the following functional equation instead:
(*)        ∀ x y ∈ R, f(f(x + y) + 2x + y) = y f(x) - f(xy).
It suffices to prove that f satisfies (*) if and only if f = 0 or f = x ↦ 2 - 2x.

The official solution works perfectly only for the case char(R) ≠ 2.
We rearrange this solution for our new functional equation.
We also present our own solution for the case char(R) = 2.

Plugging y = 1 and replacing x with x - 1 into (*) yields
(1)        ∀ x ∈ R, f(f(x) + 2x - 1) = 0.
Plugging x = 0 into (*) yields
(2)        ∀ y ∈ R, f(y + f(y)) = (y - 1) f(0).
For the case f(0) ≠ 0, this means that f(y) = 0 implies y = 1.
In particular, (1) yields f(x) = 2 - 2x for all x ∈ R.
We will split the case char(R) ≠ 2 and char(R) = 2 for the case f(0) = 0.

### Solution, case char(R) ≠ 2

Plugging x = 0 into (1) yields f(-1) = 0.
Plugging x = 1 and y = -1 into (*) afterwards yields 2f(1) = 0 → f(1) = 0.
Now, plugging in x = 1 into (*) yields
(3)  f(f(y + 1) + y + 2) = -f(y) for all y ∈ R.
In particular, if f(y) = 0 and f(y + 1) = 0, then f(y + 2) = 0.
Plugging y = 0 into (*) now yields f(f(x) + 2x) = 0 for all x ∈ R.
Combined with (1) and (3), we get
(4)       ∀ x ∈ R, f(f(x) + 2x + 1) = 0.
Now, if we plug y = -1 into (*) and use (4), we get
  0 = f(f(x - 1) + 2x - 1) = -f(x) - f(-x) for all x ∈ R.
This implies that f is odd.

Finally, plugging in x = -1 and replacing y with -y into (*) yields
  -f(y) = f(f(-y - 1) - y - 2) = -f(f(y + 1) + y + 2) for all y ∈ R.
Combined with (3), we get f(y) = 0 for all y ∈ R.
  
### Solution for the case char(R) = 2

Proceed equally in case f(0) ≠ 0 (which turns out to be impossible in this case).
From now on, assume that f(0) = 0.
Equation (*) becomes
(5)         f(f(x + y) + y) = y f(x) + f(xy).
Plugging in y = 0 into (5) yields f(f(x)) = 0 for all x ∈ R.
Plugging in x = 0 into (5) yields f(f(y) + y) = 0 for all y ∈ R instead.
Plugging in x = f(y), combined with the previous two equalities,
  yields f(f(y) y) = f(y) for all y ∈ R.
Plugging in y = f(x) instead gives us f(xf(x)) + f(x)² = 0.
Thus we have f(x f(x)) = f(x)² = f(x) for all x ∈ R.
That is, we have f(x) ∈ {0, 1} for all x ∈ R.

It remains to show that f(x) ≠ 1 for any x ∈ R.
Suppose for the sake of contradiction that f(t) = 1 for some t ∈ R.
Plugging x = y = t into (5) yields f(t²) = t + 1 ∈ {0, 1}, so t ∈ {0, 1}.
But f(0) = 0, and f(f(x)) = 0 yields f(1) ≠ 1 → f(1) = 0.
Contradiction; this implies f = 0, as desired.

## Notes

We do not need to show that the new FE implies the original FE.
That is, we just show that the original FE implies the new FE.
The case division can also be stated just by 2 ≠ 0 vs. 2 = 0.
We also try not having to change subtraction into addition many times.
-/

open function
open_locale classical

namespace IMOSL
namespace IMO2015A4

variables {R : Type*} [comm_ring R] [is_domain R]

def fn_eq (f : R → R) := ∀ x y : R, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x



namespace results

def fn_eq' (f : R → R) := ∀ x y : R, f (f (x + y) + 2 * x + y) = y * f x - f (x * y)

lemma feq'_of_feq {f : R → R} (feq : fn_eq f) : fn_eq' (f - id) :=
begin
  set g := f - id with ← hg; intros x y,
  rw sub_eq_iff_eq_add at hg,
  have h0 := feq x y,
  set z := x + f (x + y) with hz,
  rw [← eq_sub_iff_add_eq, add_sub_assoc, add_comm, ← sub_eq_iff_eq_add] at h0,
  rw [add_comm, hg, pi.add_apply, id.def, add_assoc, add_right_comm, ← two_mul] at hz,
  rw [add_assoc, ← hz]; simp [g],
  rw [h0, mul_sub, mul_comm y x, sub_sub_sub_cancel_right]
end



/-- From now on, we only work with fn_eq' -/
variables {f : R → R} (feq' : fn_eq' f)
include feq'

lemma feq'_zeroes1 (x : R) : f (f x + 2 * x - 1) = 0 :=
begin
  have h := feq' (x - 1) (1 : R),
  rwa [one_mul, mul_one, sub_self, sub_add_cancel, mul_sub_one, ← add_sub_assoc, sub_add] at h,
  change f (_ - (1 + 1 - 1)) = 0 at h,
  rwa add_sub_cancel at h
end

/-- Case 1: f(0) ≠ 0 -/
theorem case_f0_ne_0 (f0_ne_0 : f 0 ≠ 0) : f = λ x, 2 - 2 * x :=
begin
  funext x,
  have h := feq' 0 (f x + 2 * x - 1),
  rwa [zero_mul, zero_add, feq'_zeroes1 feq', zero_add, mul_zero, zero_add,
      feq'_zeroes1 feq', ← sub_one_mul, zero_eq_mul, or_iff_left f0_ne_0,
      sub_sub, sub_eq_zero, ← eq_sub_iff_add_eq] at h
end

lemma f1_eq_0 (f0_eq_0 : f 0 = 0) : f 1 = 0 :=
begin
  have h := feq'_zeroes1 feq' 0,
  rw [f0_eq_0, zero_add, mul_zero, zero_sub] at h,
  cases eq_or_ne (2 : R) 0 with R2_eq_0 R2_ne_0,
  { rw ← h; apply congr_arg,
    rw [eq_neg_iff_add_eq_zero, ← two_mul, mul_one, R2_eq_0] },
  { have h0 := feq' 1 (-1),
    rwa [add_neg_self, f0_eq_0, zero_add, two_mul, add_neg_cancel_right,
         one_mul, h, sub_zero, neg_one_mul, eq_neg_iff_add_eq_zero,
         ← two_mul, mul_eq_zero, or_iff_right R2_ne_0] at h0 },
end

/-- Case 2: f(0) = 0, 2 ≠ 0 in R -/
theorem case_f0_eq_0_R2_ne_0 (f0_eq_0 : f 0 = 0) (R2_ne_0 : (2 : R) ≠ 0) : f = 0 :=
begin

  ---- Get the equality f(f(1 + x) + (2 + x)) = -f(x).
  have h : ∀ x : R, f (f (1 + x) + (2 + x)) = - (f x) :=
  begin
    intros x,
    have h := feq' 1 x,
    rwa [f1_eq_0 feq' f0_eq_0, mul_zero, zero_sub, one_mul, mul_one, add_assoc] at h
  end,

  ---- From h, it suffices to prove that f is odd.
  suffices : ∀ x : R, f (- x) = - (f x),
  { funext x,
    have h0 := feq' (-1) (-x),
    rwa [neg_mul_neg, one_mul, this 1, f1_eq_0 feq' f0_eq_0, neg_zero, mul_zero, zero_sub,
         ← neg_add, mul_neg_one, add_assoc, ← neg_add, this, ← neg_add, this, h, neg_neg,
         eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero, or_iff_right R2_ne_0] at h0 },
  
  ---- f being odd is equivalent to f(f(x) + 2x + 1) = 0.
  suffices : ∀ x : R, f (f x + 2 * x + 1) = 0,
  { intros x,
    rw [← mul_neg_one, eq_comm, ← neg_one_mul, ← sub_eq_zero, ← feq', ← this (x - 1)],
    ring_nf },

  ---- Now show f(f(x) + 2x + 1) = 0.
  intros x,
  have h0 := feq' x 0,
  rw [add_zero, add_zero, zero_mul, mul_zero, f0_eq_0, sub_zero] at h0,
  have h1 := h (f x + 2 * x - 1),
  rw [feq'_zeroes1 feq', neg_zero, add_comm (1 : R), sub_add_cancel, h0, zero_add] at h1,
  rw ← h1; apply congr_arg,
  rw [add_comm (2 : R), add_comm_sub, add_right_inj, eq_sub_iff_add_eq, ← two_mul, mul_one]
end

/-- Case 3: f(0) = 0, 2 = 0 in R -/
theorem case_f0_eq_0_R2_eq_0 (f0_eq_0 : f 0 = 0) (R2_eq_0 : (2 : R) = 0) : f = 0 :=
begin
  have f1_eq_0 := f1_eq_0 feq' f0_eq_0,
  have add_self : ∀ x : R, x + x = 0 := λ x, by rw [← two_mul, R2_eq_0, zero_mul],
  simp only [fn_eq', R2_eq_0, zero_mul, add_zero] at feq',
  suffices : ∀ x : R, f x = 0 ∨ f x = 1,
  { funext x,
    cases this x with h h,
    exact h,
    have h0 := feq' x x,
    rw [add_self, f0_eq_0, zero_add, h, mul_one, eq_sub_iff_add_eq] at h0,
    cases this (x * x) with h1 h1,
    rw [pi.zero_apply, ← h0, h1, add_zero, f1_eq_0],
    rw [pi.zero_apply, ← h0, h1, add_self, f0_eq_0] },
  
  ---- Now prove that f(x) ∈ {0, 1} for any x ∈ R.
  intros x,
  rw [or_comm, ← mul_right_eq_self₀, ← add_left_inj (f x), add_self, add_eq_zero_iff_eq_neg],
  have h := feq' x 0,
  rw [add_zero, add_zero, zero_mul, mul_zero, f0_eq_0, sub_zero] at h,
  have h0 := feq' 0 x,
  rw [zero_add, zero_mul, f0_eq_0, sub_zero, mul_zero] at h0,
  have h1 := feq' (f x) x,
  rw [h0, zero_add, h, mul_zero, zero_sub, eq_neg_iff_eq_neg] at h1,
  have h2 := feq' x (f x),
  rwa [add_comm x (f x), h0, zero_add, h, mul_comm x, eq_comm, sub_eq_zero, h1] at h2
end

end results



/-- Final solution -/
theorem final_solution_general (f : R → R) : fn_eq f ↔ f = id ∨ f = λ x, 2 - x :=
begin
  split,
  { intros h,
    have h0 := results.feq'_of_feq h,
    cases eq_or_ne ((f - id) 0) 0 with h1 h1,
    { left; rw ← sub_eq_zero,
      cases eq_or_ne (2 : R) 0 with R2_eq_0 R2_ne_0,
      exacts [results.case_f0_eq_0_R2_eq_0 h0 h1 R2_eq_0,
              results.case_f0_eq_0_R2_ne_0 h0 h1 R2_ne_0] },
    { right; funext x,
      have h2 : (f - id) x = 2 - 2 * x := by rw results.case_f0_ne_0 h0 h1,
      rwa [pi.sub_apply, id.def, two_mul, ← sub_sub, sub_left_inj] at h2 } },
  { rintros (rfl | rfl) x y; simp only [id.def],
    rw mul_comm,
    ring }
end

end IMO2015A4
end IMOSL
