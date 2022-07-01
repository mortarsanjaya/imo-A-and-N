import algebra.algebra.basic algebra.char_p.basic tactic.field_simp

/-!
# IMO 2017 A6 (P2), Generalized Version
  
Let F be an arbitrary field.
Determine all functions f : F → F such that, for all x, y ∈ F,
  f(f(x) f(y)) + f(x + y) = f(xy).

## Solution, case char(F) ≠ 2

We refer to the solution by user "anantmudgal09" on AoPS:
  <https://artofproblemsolving.com/community/c6h1480146p8693244>.
This solution extends to the case char(F) ≠ 2.

## Notes

We have no full solution yet for the case char(F) = 2.
See the folder "A6_char_ne_2" for progress on this case.
-/

open function
open_locale classical

namespace IMOSL
namespace IMO2017A6

variables {F : Type*} [field F]

def fn_eq (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y)



namespace results

variables {f : F → F} (feq : fn_eq f)
include feq

lemma fn_lem1 : fn_eq (-f) :=
begin
  intros x y,
  simp only [pi.neg_apply],
  rw [neg_mul_neg, ← neg_add, feq],
end

lemma fn_lem2 (f_ne_0 : f ≠ 0) {x : F} (h : f x = 0) : x = 1 :=
begin
  contrapose f_ne_0,
  rw not_not,
  suffices : f 0 = 0,
  { funext x,
    have h0 := feq x 0,
    rwa [mul_zero, add_zero, this, mul_zero, this, zero_add] at h0 },
  suffices : x + x / (x - 1) = x * (x / (x - 1)),
  { have h0 := feq x (x / (x - 1)),
    rwa [h, zero_mul, this, add_left_eq_self] at h0 },
  change x ≠ 1 at f_ne_0,
  rw [← sub_ne_zero] at f_ne_0,
  field_simp,
  rw [mul_sub_one, sub_add_cancel]
end

lemma fn_lem3 (f_ne_0 : f ≠ 0) : f (f 0 ^ 2) = 0 :=
begin
  have h := feq 0 0,
  rwa [add_zero, mul_zero, add_left_eq_self, ← sq] at h
end

lemma fn_lem4 (f_ne_0 : f ≠ 0) : f 0 ^ 2 = 1 :=
  fn_lem2 feq f_ne_0 (fn_lem3 feq f_ne_0)

lemma fn_lem5 : f 1 = 0 :=
begin
  by_cases h : f = 0,
  rw [h, pi.zero_apply],
  rw [← fn_lem4 feq h, fn_lem3 feq h]
end

lemma fn_lem6 (f0_eq_1 : f 0 = 1) (x : F) : f x = 0 ↔ x = 1 :=
begin
  split,
  apply fn_lem2 feq,
  rintros rfl,
  rw [pi.zero_apply, eq_comm] at f0_eq_1,
  exact one_ne_zero f0_eq_1,
  rintros rfl; exact fn_lem5 feq
end

lemma fn_lem7 (f0_eq_1 : f 0 = 1) (x : F) : f (x + 1) = f x - 1 :=
begin
  have h := feq x 1,
  rwa [fn_lem5 feq, mul_zero, mul_one, f0_eq_1, add_comm, ← eq_sub_iff_add_eq] at h
end

lemma fn_lem8 (f0_eq_1 : f 0 = 1) (f_inj : injective f) : f = λ x, 1 - x :=
begin
  have h : ∀ x : F, f (f x) + f x = 1 :=
  begin
    intros x,
    have h := feq x 0,
    rwa [mul_zero, f0_eq_1, mul_one, add_zero] at h
  end,
  funext x,
  rw [← h x, eq_sub_iff_add_eq, add_comm, add_left_inj],
  apply f_inj,
  rw [← add_left_inj (f (f x)), h, add_comm, h]
end

lemma fn_lem9 (f0_eq_1 : f 0 = 1) (x : F) : f (x - 1) = f x + 1 :=
  by rw [← sub_eq_iff_eq_add, ← fn_lem7 feq f0_eq_1, sub_add_cancel]

lemma fn_lem10 (f0_eq_1 : f 0 = 1) (x : F) : f (f x * (1 + 1)) + f x + 1 = f (-x) :=
  by rw [← mul_neg_one, ← feq x (-1), add_assoc, ← sub_eq_add_neg,
         fn_lem9 feq f0_eq_1, ← zero_sub, fn_lem9 feq f0_eq_1, f0_eq_1]

lemma fn_lem11 (char_ne_2 : ring_char F ≠ 2) (f0_eq_1 : f 0 = 1) {x : F} (h : f x = f (-x)) : x = 0 :=
begin
  have h0 := fn_lem10 feq f0_eq_1 x,
  rw [add_right_comm, h, add_left_eq_self, ← fn_lem9 feq f0_eq_1, fn_lem6 feq f0_eq_1,
      sub_eq_iff_eq_add, mul_left_eq_self₀, ← sub_eq_zero, ← fn_lem7 feq f0_eq_1,
      fn_lem6 feq f0_eq_1, add_left_eq_self, neg_eq_zero] at h0,
  cases h0 with h0 h0,
  exact h0,
  exfalso; exact ring.two_ne_zero char_ne_2 h0
end

lemma fn_lem12 (char_ne_2 : ring_char F ≠ 2) (f0_eq_1 : f 0 = 1) : injective f :=
begin
  intros x y h,
  have h0 : f (-x) = f (-y) := by rw [← fn_lem10 feq f0_eq_1, h, fn_lem10 feq f0_eq_1],
  have h1 := feq x (-y),
  rw [h, ← h0, mul_neg, ← neg_mul, mul_comm, ← feq (-x) y, add_right_inj] at h1,
  rw ← add_neg_eq_zero; apply fn_lem11 feq char_ne_2 f0_eq_1,
  rw [neg_add, neg_neg, h1]
end

end results



/-- Final solution -/
theorem final_solution_char_ne_2 (char_ne_2 : ring_char F ≠ 2) (f : F → F) :
  fn_eq f ↔ f = 0 ∨ (f = λ x, x - 1) ∨ (f = λ x, 1 - x) :=
begin
  split,
  { intros feq,
    cases eq_or_ne f 0 with h h,
    left; exact h,
    right,
    have h0 := results.fn_lem4 feq h,
    rw [sq_eq_one_iff] at h0,
    cases h0 with h0 h0,
    right; exact results.fn_lem8 feq h0 (results.fn_lem12 feq char_ne_2 h0),
    left,
    rw [eq_neg_iff_eq_neg, eq_comm, ← pi.neg_apply f 0] at h0,
    have h1 := results.fn_lem1 feq,
    replace h1 := results.fn_lem8 h1 h0 (results.fn_lem12 h1 char_ne_2 h0),
    rw [eq_comm, eq_neg_iff_eq_neg] at h1,
    rw h1; funext x; simp only [pi.neg_apply, neg_sub, sub_left_inj] },
  { rintros (rfl | rfl | rfl) x y; simp,
    all_goals { ring } }
end


end IMO2017A6
end IMOSL
