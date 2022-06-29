import IMO2017.A6.A6_general algebra.char_p.basic

/-!
# IMO 2017 A6 (P2), Generalized Version, case char(F) ≠ 2.
  
## Solution (continue from the general case)

From f(x + 1) = f(x) - 1, we know that f(x + n) = f(x) - n ∀ x ∈ F, n ∈ ℤ.
In particular, for n ∈ ℤ, f(x) = n iff x = 1 - n.
Now, plugging in y = -1 yields f(2 f(x)) + f(x) + 1 = f(-x) for all x ∈ F.
In particular, for any x, y ∈ F, f(x) = f(y) implies f(-x) = f(-y).
On the other hand, this implies
  f(x - y) = f(-xy) - f(f(x) f(-y)) = f(-xy) - f(f(-x) f(y)) = f(y - x).
Finally, for any t ∈ F, f(t) = f(-t) implies
  f(2 f(t)) + 1 = 0 → f(2 f(t)) = -1 → 2 f(t) = 2 → f(t) = 1 → t = 0.
Thus x - y = 0 → x = y, proving that f is indeed injective.
Note that 2 f(t) = 2 → f(t) = 1 works only because char(F) ≠ 2.

# Implementation details

1. We do not need the whole f(x) = n ↔ x = 1 - n result.
We actually only need f(-1) = 2, f(x) = -1 → x = 2, and f(x) = 1 → x = 0.
We will write the first one as f(-1) = 1 + 1.

2. We will prove f(t) = f(-t) ↔ t = 0 instead of f(t) = f(-t) → t = 0.
We will also prove this result before f(x) = f(y) → f(x - y) = f(y - x).
In particular we can combine the latter step directly into injectivity.
-/

open function
open_locale classical

namespace IMOSL
namespace IMO2017A6

variables {F : Type*} [field F]



---- Injectivity result for char(F) ≠ 2.
---- This implies no other functions satisfying fn_eq
namespace results
namespace case_char_ne_2

variables {f : F → F} (feq : fn_eq f)
include feq

lemma fn_lem1 :
  f 0 = 1 → ∀ x : F, f (x - 1) = f x + 1 :=
begin
  intros h x,
  rw [← sub_eq_iff_eq_add, ← results.fn_general4_1 feq h, sub_add_cancel],
end

lemma fn_lem2 :
  f 0 = 1 → ∀ x : F, f (f x * (1 + 1)) + f x + 1 = f (-x) :=
begin
  intros h x,
  have h0 : f (-1) = 1 + 1 :=
    by rw [← sub_eq_iff_eq_add, ← results.fn_general4_1 feq h, neg_add_self, h],
  rw [← h0, add_assoc, ← fn_lem1 feq h, sub_eq_add_neg, feq, mul_neg_one],
end

lemma fn_lem3 (char_ne_2 : ring_char F ≠ 2) :
  f 0 = 1 → ∀ x : F, f x = f (-x) ↔ x = 0 :=
begin
  intros h x,
  have h0 := fn_lem2 feq h x,
  rw [add_right_comm, ← eq_sub_iff_add_eq, ← fn_lem1 feq h] at h0,
  have X : f ≠ 0,
  { intros h1,
    rw [h1, pi.zero_apply] at h,
    exact zero_ne_one h },
  rw [eq_comm, ← sub_eq_zero, ← h0, results.fn_general3 feq X, sub_eq_iff_eq_add,
      mul_left_eq_self₀, or_iff_left, ← sub_eq_zero, ← results.fn_general4_1 feq h,
      results.fn_general3 feq X, add_left_eq_self],
  exact ring.two_ne_zero char_ne_2,
end

lemma fn_lem4 (char_ne_2 : ring_char F ≠ 2) :
  f 0 = 1 → injective f :=
begin
  intros h x y h0,
  have h1 : f (-x) = f (-y) := by rw [← fn_lem2 feq h, h0, fn_lem2 feq h],
  have h2 := feq x (-y),
  rw [h0, ← h1, mul_neg, ← neg_mul, mul_comm, ← feq (-x) y, add_right_inj] at h2,
  rw [← add_neg_eq_zero, ← fn_lem3 feq char_ne_2 h, neg_add, neg_neg, h2],
end

theorem fn_sol (char_ne_2 : ring_char F ≠ 2) :
  f 0 = 1 → f = 1 - id :=
begin
  intros h,
  apply results.fn_general4 feq h,
  exact fn_lem4 feq char_ne_2 h,
end

end case_char_ne_2
end results







---- Final solution, case char(F) ≠ 2
theorem final_solution_char_ne_2 (char_ne_2 : ring_char F ≠ 2) :
  set_of fn_eq = ({0, 1 - id, id - 1} : set (F → F)) :=
begin
  rw set.ext_iff; intros f,
  simp only [set.mem_set_of_eq, set.mem_insert_iff, set.mem_singleton_iff]; split,

  ---- All functions satisfying fn_eq are in the RHS set
  { intros h,
    by_cases h0 : f = 0,
    left; exact h0,
    right,
    have h1 := results.fn_general3_3 h h0,
    rw sq_eq_one_iff at h1,
    cases h1 with h1 h1,
    left; exact results.case_char_ne_2.fn_sol h char_ne_2 h1,
    right,
    rw [← neg_sub, eq_neg_iff_eq_neg, eq_comm],
    apply results.case_char_ne_2.fn_sol (results.fn_general1 h) char_ne_2,
    rwa [pi.neg_apply, h1, neg_neg] },

  ---- All functions on the RHS satisfy fn_eq
  { intros h,
    rcases h with h | h | h,
    rw h; exact results.fn_ans1,
    rw h; exact results.fn_ans2,
    rw h; exact results.fn_ans3 },
end

end IMO2017A6
end IMOSL
