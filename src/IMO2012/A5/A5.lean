import
  data.real.basic
  data.real.nnreal
  data.real.sqrt
  algebra.algebra.basic
  algebra.char_p.basic
  algebra.char_p.two
  data.polynomial.basic

/-!
# IMO 2012 A5, Generalized Version

Let R be an integral domain.
Find all functions f : ℝ → R such that, for all x, y ∈ ℝ,
        f(1 + xy) - f(x + y) = f(x) f(y).

## Answer
1. f = 0,
2. f = x ↦ φ(x) - 1 for some φ : ℝ →+* R, and
3. f = x ↦ φ(x^2) - 1 for some φ : ℝ≥0 →+* R.

Note that, if char(R) ≠ 0, then there are no ring/semiring homomorphism from ℝ or ℝ≥0 to R.
In this case, the only answer is f = 0.
When R = ℝ, the identity map is the only ring homomorphism ℝ → ℝ.
Also, the natural lift map x ∈ ℝ≥0 ↦ x ∈ ℝ is the only semiring homomorphism ℝ≥0 → ℝ.

## Solution

See <https://www.imo-official.org/problems/IMO2012SL.pdf>.
The whole official solution works for the case f(-1) ≠ 0, except for the case char(R) = 2.
It proves that f + 1 is in fact a ring homomorphism.
For char(R) = 2, the solution works up to g(x + 2) - g(x) = 2 = 0 ↔ f(x + 2) = f(x).
Then one gets an instant contradiction since f(-1) = f(1) = 0.

We will not work with g = f + 1 for the case f(-1) ≠ 0; we will only use f for our solution.
We will deal with the case f(-1) = 0 below.

### Case f(-1) = 0

Plugging y = -1 and replacing x with x + 1 reveals to us that f is in fact even.
In particular, f(1) = f(-1) = 0.
Plugging y = 0 into the original equation now yields f(x) f(0) = -f(x) for all x ∈ ℝ.
Since R is a domain, this forces either f(0) = -1 or f = 0.
In the former case, we are done, so we will now assume the latter case.

We now employ a trick that works whenever f is an even function with domain ℝ:
  there exists a function g : ℝ≥0 → R such that f(x) = g(x^2) for all x ∈ ℝ.
Indeed, such g is defined by g(x) = f(sqrt(x)) for any x ≥ 0.
Then the original equation becomes
(1)       g((1 + xy)^2) - g((x + y)^2) = g(x^2) g(y^2).
Changing y with -y gives us
(2)       g((1 + xy)^2) - g((1 - xy)^2) = g((x + y)^2) - g((x - y)^2)
Now note that, for every u, v ≥ 0, there exists x, y ∈ ℝ such that u = (x - y)^2 and v = 4xy.
Indeed, the equation becomes |x - y| = sqrt(u) and |x + y| = sqrt(u + v).
So, one can take x = (sqrt(u + v) + sqrt(u))/2 and y = (sqrt(u + v) - sqrt(u))/2.
Thus, for all u, v ≥ 0,
        g((1 + v/4)^2) - g((1 - v/4)^2) = g(u + v) - g(u).
In particular, the left hand side is also equal to g(v) - g(0), so for all u, v ≥ 0,
(4)     g(u + v) = g(u) + g(v) - g(0).
Since g(0) = f(0) = -1, this means g + 1 is an additive monoid homomorphism ℝ≥0 → R.
For convenience, denote φ = g + 1.

Since φ is an additive monoid homomorphism, equation (1) now reads as
        1 + φ((xy)^2) - φ(x^2) - φ(y^2) = (φ(x^2) - 1) (φ(y^2) - 1).
Note that φ(1) = 1 since g(1) = f(1) = 0.
Rearranging gives us φ((xy)^2) = φ(x^2) φ(y^2) for any x, y ∈ ℝ.
So φ is also multiplicative, which means φ is in fact a semiring homomorphism ℝ≥0 → R.
It is easy to check that the converse is true: x ↦ φ(x^2) + 1 satisfy the original equation.

## Note

For R = ℝ, pretty much f = 0, f = x ↦ x - 1, and f = x ↦ x^2 - 1 are the only solutions.
Indeed, there is only one semiring homomorphism ℝ≥0 → ℝ; the natural lift.

The original question also contained the condition f(-1) ≠ 0.
-/

open function real
open_locale classical

namespace IMOSL
namespace IMO2012A5

variables {R : Type*} [comm_ring R] [is_domain R]

def fn_eq (f : ℝ → R) := ∀ x y : ℝ, f (1 + x * y) - f(x + y) = f x * f y



namespace extra

/-- For any x ≤ 0, there exists u ∈ ℝ such that x = 1 + u - u^2 -/
lemma real_poly_range1 {x : ℝ} (h : x ≤ 0) : ∃ u : ℝ, x = 1 + u * (1 - u) :=
begin
  use [(sqrt (5 - 4 * x) + 1) / 2],
  field_simp; ring_nf,
  rw [sq_sqrt, neg_add, neg_neg, neg_add_cancel_right],
  linarith only [h] ---- Too lazy to explicitly write the steps
end

/-- For any u, v ≥ 0, there exists x, y ∈ ℝ such that u = (x - y)^2 and v = 4xy. -/
lemma real_mv_poly_range1 {u v : ℝ} (h : 0 ≤ u) (h0 : 0 ≤ v) :
  ∃ x y : ℝ, u = (x - y) ^ 2 ∧ v = 4 * (x * y) :=
begin
  use [(sqrt (u + v) + sqrt u) / 2, (sqrt (u + v) - sqrt u) / 2],
  split; field_simp; ring_nf,
  rw sq_sqrt h,
  rw [sq_sqrt (add_nonneg h0 h), sq_sqrt h, mul_add, add_sub_cancel]
end



end extra



private lemma lem1_1 {f : ℝ → R} (feq : fn_eq f) : f 1 = 0 :=
begin
  have h := feq 1 1,
  rwa [mul_one, sub_self, zero_eq_mul_self] at h
end

private lemma lem1_2 {f : ℝ → R} (feq : fn_eq f) (h : f 0 ≠ -1) : f = 0 :=
begin
  funext x,
  have h0 := feq x 0,
  rwa [mul_zero, add_zero, lem1_1 feq, zero_sub, add_zero, ← mul_neg_one,
       mul_eq_mul_left_iff, eq_comm, or_iff_right h] at h0
end

private lemma lem1_3 {f : ℝ → R} (feq : fn_eq f) (x : ℝ) :
  f x - f (-x) = f (-1) * f (1 - x) :=
begin
  have h := feq (-1) (1 - x),
  rwa [neg_one_mul, neg_sub, add_sub_cancel'_right, ← add_sub_assoc, neg_add_self, zero_sub] at h
end



private lemma lem2_1 {f : ℝ → R} (feq : fn_eq f) (h : f (-1) ≠ 0) : f 0 = -1 :=
  by contrapose! h; rw [lem1_2 feq h, pi.zero_apply]

private lemma lem2_2 {f : ℝ → R} (feq : fn_eq f) (h : f (-1) ≠ 0) (x : ℝ) : f (2 - x) = -f x :=
begin
  have h0 := lem1_3 feq (1 - x),
  have h1 := lem1_3 feq (-(1 - x)),
  rwa [neg_neg, ← neg_sub, h0, ← mul_neg, mul_eq_mul_left_iff, or_iff_left h,
       sub_sub_cancel, sub_neg_eq_add, ← add_sub_assoc, eq_comm] at h1
end

private lemma lem2_3 {f : ℝ → R} (feq : fn_eq f) (h : f (-1) ≠ 0) (x : ℝ) : f (x + 2) = f x + 2 :=
begin
  revert x; suffices : ∀ x : ℝ, x ≤ 0 → f (x + 2) - f x = f 3 - f 1,
  { have h0 := lem2_2 feq h 0,
    rw [sub_zero, lem2_1 feq h, neg_neg] at h0,
    have h1 := this 0 (le_refl 0),
    rw [← h1, zero_add, h0, lem2_1 feq h, sub_neg_eq_add, ← bit0] at this,
    clear h1; intros x,
    rw ← sub_eq_iff_eq_add',
    cases le_or_lt x 0 with h1 h1,
    exact this x h1,
    rw [← neg_sub, sub_eq_add_neg, ← lem2_2 feq h, ← sub_sub, sub_sub_cancel_left,
        neg_add, ← lem2_2 feq h, ← sub_eq_add_neg, sub_eq_add_neg 2 x, add_comm, this],
    exact le_of_lt (neg_lt_zero.mpr h1) },
  intros x h0,
  replace h0 := extra.real_poly_range1 h0,
  rcases h0 with ⟨u, rfl⟩,
  rw sub_eq_sub_iff_sub_eq_sub,
  nth_rewrite 6 ← add_sub_cancel'_right u 1,
  rw [feq, ← neg_mul_neg (f u), ← lem2_2 feq h, ← lem2_2 feq h, ← feq],
  congr' 2; ring
end

private lemma lem2_4 [char_p R 2] {f : ℝ → R} (feq : fn_eq f) : f (-1) = 0 :=
begin
  by_contra h,
  have h0 := lem2_3 feq h (-1),
  rw [bit0, neg_add_cancel_comm_assoc, char_two.two_eq_zero, add_zero, lem1_1 feq, eq_comm] at h0,
  exact h h0
end

private lemma lem2_5 {f : ℝ → R} (feq : fn_eq f) (h : f (-1) ≠ 0) (x : ℝ) : f (-x) = -(2 + f x) :=
begin
  have h0 := lem2_3 feq h (-x),
  rw [add_comm, ← sub_eq_add_neg, lem2_2 feq h, ← sub_eq_iff_eq_add] at h0,
  rw [← h0, sub_eq_add_neg, add_comm, neg_add]
end

private lemma lem2_6 (char_ne_2 : ring_char R ≠ 2) {f : ℝ → R} (feq : fn_eq f) (h : f (-1) ≠ 0)
  (x y : ℝ) : f (x + y) = f x + f y + 1 :=
begin
  have h0 := feq (-x) (-y),
  rw [neg_mul_neg, ← neg_add, lem2_5 feq h, sub_neg_eq_add, lem2_5 feq h, lem2_5 feq h,
      neg_mul_neg, add_mul, mul_add, mul_add, ← feq, ← sub_eq_zero] at h0,
  replace h0 : 2 * (f (x + y) - (f x + f y + 1)) = 0 := by rw ← h0; ring,
  rwa [mul_eq_zero, or_iff_right (ring.two_ne_zero char_ne_2), sub_eq_zero] at h0
end

private lemma lem2_7 (char_ne_2 : ring_char R ≠ 2) {f : ℝ → R} (feq : fn_eq f) (h : f (-1) ≠ 0) :
  ∃ φ : ℝ →+* R, f = φ - 1 :=
begin
  use f + 1; simp,
  exact lem1_1 feq,
  intros x y,
  have h0 := feq x y,
  rw [sub_eq_iff_eq_add, lem2_6 char_ne_2 feq h, lem1_1 feq, zero_add] at h0,
  rw [h0, lem2_6 char_ne_2 feq h, add_one_mul, mul_add_one, add_assoc, add_assoc],
  rw [lem2_1 feq h, neg_add_self],
  intros x y,
  rw [lem2_6 char_ne_2 feq h, add_assoc, add_add_add_comm]
end




end IMO2012A5
end IMOSL
