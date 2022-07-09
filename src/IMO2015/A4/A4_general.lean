import algebra.algebra.basic algebra.char_p.two

/-!
# IMO 2015 A4 (P5), Generalized Version
  
Let R be a (non-trivial, not necessarily commutative) domain.
Find all functions f : R → R such that, for all x, y ∈ R,
  f(x + f(x + y)) + f(xy) = x + f(x + y) + f(x) y.

## Answer

f = id and f = x ↦ 2 - x.

## lem2_5ution

See <http://www.imo-official.org/problems/IMO2015SL.pdf>.
However, instead of working with f, we work with f - id.
That is, we will lem2_5ve the following functional equation instead:
(*)        ∀ x y ∈ R, f(f(x + y) + 2x + y) = f(x) y - f(xy).
It suffices to prove that f satisfies (*) if and only if f = 0 or f = x ↦ 2 - 2x.

The official lem2_5ution works only for the case char(R) ≠ 2.
However, it requires at most a minor modification to handle the case where R is not commutative.
We rearrange this lem2_5ution for our new functional equation.
We also present our own lem2_5ution for the case char(R) = 2.

Plugging y = 1 and replacing x with x - 1 into (*) yields
(1)        ∀ x ∈ R, f(f(x) + 2x - 1) = 0.
Plugging x = 0 into (*) yields
(2)        ∀ y ∈ R, f(y + f(y)) = (y - 1) f(0).
For the case f(0) ≠ 0, this means that f(y) = 0 implies y = 1.
In particular, (1) yields f(x) = 2 - 2x for all x ∈ R.
We will split the case char(R) ≠ 2 and char(R) = 2 for the case f(0) = 0.

### lem2_5ution, case char(R) ≠ 2

Plugging x = 0 into (1) yields f(-1) = 0.
Plugging x = 1 and y = -1 into (*) afterwards yields 2f(1) = 0 → f(1) = 0.
Now, plugging in x = 1 into (*) yields
(3)       ∀ y ∈ R, f(f(y + 1) + y + 2) = -f(y)
In particular, if f(y) = 0 and f(y + 1) = 0, then f(y + 2) = 0.

Plugging y = 0 into (*) now yields f(f(x) + 2x) = 0 for all x ∈ R.
Combined with (1) and (3), we get
(4)       ∀ x ∈ R, f(f(x) + 2x + 1) = 0.
Now, if we plug y = -1 into (*) and use (4), we get
  0 = f(f(x - 1) + 2x - 1) = -f(x) - f(-x) for all x ∈ R.
This implies that f is odd.

Finally, plugging x = -1 and replacing y with -y into (*) yields
  -f(y) = f(f(-y - 1) - y - 2) = -f(f(y + 1) + y + 2) for all y ∈ R.
Combined with (3), we get f(y) = 0 for all y ∈ R.
  
### lem2_5ution, case char(R) = 2

Proceed equally in case f(0) ≠ 0 (which turns out to be impossible in this case).
From now on, assume that f(0) = 0.
Equation (*) becomes
(5)         f(f(x + y) + y) = f(x) y + f(xy).
Plugging x = y = 1 into (5) yields f(1) = 0.
Now, plugging x = y + 1 into (5) yields f(y) = f(y + 1) y + f(y^2 + y).
Replacing y with y + 1, we get f(y + 1) + f(y) (y + 1) = f(y^2 + y) = f(y) + f(y + 1) y.
This means, for any y ∈ R, we have
(6)         f(y + 1) (y + 1) = f(y) y.

Now, plugging y = 0 into (5) yields f(f(x)) = 0.
Plugging x = 0 into (5) yields f(f(y) + y) = 0.
Then plugging x = f(y) into (5) yields
(7)         f(f(y) y) = f(y).
Then we have f(y + 1) = f(f(y + 1) (y + 1)) = f(f(y) y) = f(y) by (6).
But then f(y) (y + 1) = f(y) y → f(y) = 0, as desired.

## Notes

1. We do not need to show that the new FE implies the original FE.
That is, we just show that the original FE implies the new FE.

2. In the original formulation, we have y f(x) instead of f(x) y.
The identity function satisfy the equation in that case if and only if R is commutative.
Changing y f(x) to f(x) y removes the necessity of R being commutative.

3. We also have an alternative lem2_5ution for the case char(R) = 2 that works when R is commutative.
See below; we will not implement this alternative lem2_5ution.

### Alternative lem2_5ution, case char(R) = 2, R commutative, f(0) = 0

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
-/

open function
open_locale classical

namespace IMOSL
namespace IMO2015A4

variables {R : Type*} [ring R] [is_domain R]

def fn_eq (f : R → R) := ∀ x y : R, f (x + f (x + y)) + f (x * y) = x + f (x + y) + f x * y



section results

private def fn_eq1 (f : R → R) := ∀ x y : R, f (f (x + y) + 2 * x + y) = f x * y - f (x * y)

private lemma lem1_1 {f : R → R} (feq : fn_eq f) : fn_eq1 (f - id) :=
begin
  set g := f - id with ← hg; intros x y,
  rw sub_eq_iff_eq_add at hg,
  have h0 := feq x y,
  set z := x + f (x + y) with hz,
  rw [← eq_sub_iff_add_eq, add_sub_assoc, add_comm, ← sub_eq_iff_eq_add] at h0,
  rw [add_comm, hg, pi.add_apply, id.def, add_assoc, add_right_comm, ← two_mul] at hz,
  rw [add_assoc, ← hz]; simp [g],
  rw [h0, sub_mul, sub_sub_sub_cancel_right]
end

private lemma lem1_2 {f : R → R} (feq1 : fn_eq1 f) (x : R) : f (f x + 2 * x - 1) = 0 :=
begin
  have h := feq1 (x - 1) (1 : R),
  rwa [mul_one, mul_one, sub_self, sub_add_cancel, mul_sub_one, ← add_sub_assoc, sub_add] at h,
  change f (_ - (1 + 1 - 1)) = 0 at h,
  rwa add_sub_cancel at h
end

/-- Case 1: f(0) ≠ 0 -/
private theorem lem1_3 {f : R → R} (feq1 : fn_eq1 f) (f0_ne_0 : f 0 ≠ 0) : f = λ x, 2 - 2 * x :=
begin
  funext x,
  have h := feq1 0 (f x + 2 * x - 1),
  rwa [zero_mul, zero_add, lem1_2 feq1, zero_add, mul_zero, zero_add,
      lem1_2 feq1, ← mul_sub_one, zero_eq_mul, or_iff_right f0_ne_0,
      sub_sub, sub_eq_zero, ← eq_sub_iff_add_eq] at h
end



section case_char_ne_2

variable char_ne_2 : ring_char R ≠ 2
include char_ne_2

variables {f : R → R} (feq1 : fn_eq1 f) (f0_eq_0 : f 0 = 0)
include feq1 f0_eq_0

private lemma lem2_1 : f 1 = 0 :=
begin
  have h := lem1_2 feq1 0,
  rw [f0_eq_0, zero_add, mul_zero, zero_sub] at h,
  have h0 := feq1 1 (-1),
  rwa [add_neg_self, f0_eq_0, zero_add, two_mul, add_neg_cancel_right,
       one_mul, h, sub_zero, mul_neg_one, eq_neg_iff_add_eq_zero, ← two_mul,
       mul_eq_zero, or_iff_right (ring.two_ne_zero char_ne_2)] at h0
end

private lemma lem2_2 (x : R) : f (f (1 + x) + 2 + x) = - f x :=
begin
  have h := feq1 1 x,
  rwa [one_mul, mul_one, lem2_1 char_ne_2 feq1 f0_eq_0, zero_mul, zero_sub] at h
end

private lemma lem2_3 (x : R) : f (f x + 2 * x + 1) = 0 :=
begin
  have lem2_1 := lem2_1 char_ne_2 feq1 f0_eq_0,
  have h := feq1 x 0,
  rw [add_zero, add_zero, mul_zero, mul_zero, f0_eq_0, sub_zero] at h,
  have h0 := feq1 1 (f x + 2 * x - 1),
  rwa [one_mul, lem1_2 feq1 x, sub_zero, lem2_1, zero_mul, add_comm (1 : R) _,
       sub_add_cancel, h, zero_add, two_mul, add_comm, sub_add_add_cancel] at h0
end

private lemma lem2_4 (x : R) : f (- x) = - (f x) :=
begin
  have h := lem2_3 char_ne_2 feq1 f0_eq_0 (x + -1),
  rw [mul_add, two_mul (-1 : R), add_assoc, add_assoc, neg_add_cancel_comm] at h,
  have h0 := feq1 x (-1),
  rwa [add_assoc, h, eq_comm, sub_eq_zero, mul_neg_one, mul_neg_one, eq_comm] at h0
end

/-- Case 2: f(0) = 0, char(R) ≠ 2 -/
private theorem lem2_5 : f = 0 :=
begin
  funext x,
  have lem2_4 := lem2_4 char_ne_2 feq1 f0_eq_0,
  have h := feq1 (-1) (-x),
  rwa [neg_mul_neg, one_mul, lem2_4, lem2_1 char_ne_2 feq1 f0_eq_0, neg_zero, zero_mul,
       zero_sub, ← neg_add, lem2_4, mul_neg_one, ← neg_add, ← neg_add, lem2_4,
       lem2_2 char_ne_2 feq1 f0_eq_0, neg_neg, eq_neg_iff_add_eq_zero, ← two_mul,
       mul_eq_zero, or_iff_right (ring.two_ne_zero char_ne_2)] at h
end

end case_char_ne_2



section case_char_eq_2

variable [char_p R 2]

/-- Simplified version of `feq1` in the case where 2 = 0 in R -/
private def fn_eq2 (f : R → R) := ∀ x y : R, f (f (x + y) + y) = f x * y - f (x * y)

variables {f : R → R} (feq2 : fn_eq2 f) (f0_eq_0 : f 0 = 0)
include feq2 f0_eq_0

private lemma lem3_1 : f 1 = 0 :=
begin
  have h := feq2 (-1) 1,
  rwa [neg_add_self, f0_eq_0, zero_add, mul_one, mul_one, sub_self] at h
end

private lemma lem3_2 (x : R) : f x + f (x + 1) * x = f ((x + 1) * x) :=
begin
  have h := feq2 (x + 1) x,
  rwa [add_comm (x + 1) x, ← add_assoc, char_two.add_self_eq_zero, zero_add, lem3_1 feq2 f0_eq_0,
       zero_add, char_two.sub_eq_add, ← sub_eq_iff_eq_add', char_two.sub_eq_add] at h
end

private lemma lem3_3 (x : R) : f (x + 1) * (x + 1) = f x * x :=
begin
  have h := lem3_2 feq2 f0_eq_0 (x + 1),
  rwa [add_assoc, char_two.add_self_eq_zero, add_zero, mul_add_one x, ← add_one_mul,
       ← lem3_2 feq2 f0_eq_0, add_comm (f x), mul_add_one, ← add_assoc, add_left_inj,
       ← eq_sub_iff_add_eq', char_two.sub_eq_add, ← mul_add_one, eq_comm] at h
end

private lemma lem3_4 (x : R) : f (f x * x) = f x :=
begin
  have h := feq2 x 0,
  rw [add_zero, add_zero, mul_zero, mul_zero, f0_eq_0, sub_zero] at h,
  have h0 := feq2 0 x,
  rw [zero_add, zero_mul, f0_eq_0, zero_mul, sub_zero] at h0,
  have h1 := feq2 (f x) x,
  rwa [h0, zero_add, h, zero_mul, char_two.sub_eq_add, zero_add, eq_comm] at h1
end

/-- Case 3: f(0) = 0, char(R) = 2 -/
private theorem lem3_5 : f = 0 :=
begin
  funext x,
  have h := lem3_4 feq2 f0_eq_0 (x + 1),
  rw [lem3_3 feq2 f0_eq_0, lem3_4 feq2 f0_eq_0] at h,
  have h0 := lem3_3 feq2 f0_eq_0 x,
  rwa [← h, mul_add_one, add_right_eq_self] at h0
end

end case_char_eq_2

end results



/-- Final lem2_5ution -/
theorem final_solution_general (f : R → R) : fn_eq f ↔ f = id ∨ f = λ x, 2 - x :=
begin
  split,
  { intros h,
    replace h := lem1_1 h,
    cases eq_or_ne ((f - id) 0) 0 with h0 h0,
    { left; rw ← sub_eq_zero,
      cases ne_or_eq (ring_char R) 2 with char_ne_2 char_eq_2,
      exact lem2_5 char_ne_2 h h0,
      rw ring_char.eq_iff at char_eq_2,
      resetI,
      simp only [fn_eq1, char_two.two_eq_zero, zero_mul, add_zero] at h,
      exact lem3_5 h h0 },
    { right; funext x,
      have h1 : (f - id) x = 2 - 2 * x := by rw lem1_3 h h0,
      rwa [pi.sub_apply, id.def, two_mul, ← sub_sub, sub_left_inj] at h1 } },
  { rintros (rfl | rfl) x y; simp only [id.def],
    rw [← add_sub_assoc x, add_sub_add_left_eq_sub, sub_sub_cancel, sub_mul, sub_add_sub_comm,
        add_sub_assoc, ← sub_sub, two_mul, add_sub_cancel, add_sub_left_comm] }
end

end IMO2015A4
end IMOSL
