import
  algebra.algebra.basic

namespace IMO2017A6

universe u
variable {F : Type u}
variable [field F]

/--
  IMO 2017 A6 (P2), Generalized Version
  Let F be an arbitrary field.
  Determine all functions f : F → F such that, for all x, y ∈ F,
          f(f(x) f(y)) + f(x + y) = f(xy).
          
  Note:
  
  1. The case char F ≠ 2 is solved.
     See file "A6_char_ne_2.lean", with two main theorems:
        IMO2017A6_sol_char_ne_2, IMO2017A6_sol_R
     We refer to the solution by user "anantmudgal09" on AoPS:
       https://artofproblemsolving.com/community/c6h1480146p8693244.
     Note that the solution extends to the case char F ≠ 2.
     The same file will also contain the result for F = ℝ.

  2. The case char F = 2 is still open.
     See the folder "A6_char_eq_2".

  3. This file contains the statement of the functional equation and
       lemmas that are usable for both case char F ≠ 2 and char F = 2.
-/
def fn_eq (f : F → F) :=
  ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y)



open function
open_locale classical







---- General lemmas
namespace general

variable {f : F → F}
variable feq : fn_eq f
include feq



---- Show that f satisfies the equation iff -f also satisfies the equation
theorem fn_thm1 :
  fn_eq (-f) :=
begin
  intros x y,
  simp only [pi.neg_apply],
  rw [neg_mul_neg, ← neg_add, feq],
end



---- Show that either f x = 0 → x = 1 or ∀ x, f x = 0
theorem fn_thm2 :
  (∃ x : F, x ≠ 1 ∧ f x = 0) → f = 0 :=
begin
  intros h; suffices : f 0 = 0,
  { apply funext; intros x,
    have h0 := feq x 0,
    rwa [mul_zero, add_zero, this, mul_zero, this, zero_add] at h0 },
  rcases h with ⟨c, h, h0⟩,
  rw ← sub_ne_zero at h,
  let d := c / (c - 1),
  have h1 := feq c d,
  suffices : c + d = c * d,
    rwa [this, add_left_eq_self, h0, zero_mul] at h1,
  calc c + c / (c - 1) = (c * (c - 1) + c) / (c - 1) : by rw add_div_eq_mul_add_div _ _ h
  ... = (c * (c - 1) + c * 1) / (c - 1) : by rw mul_one
  ... = c * (c - 1 + 1) / (c - 1) : by rw ← mul_add
  ... = c * c / (c - 1) : by rw sub_add_cancel
  ... = c * (c / (c - 1)) : by rw mul_div_assoc,
end



---- Now assume that f ≠ 0. Show that f x = 0 ↔ x = 1
lemma fn_lem3_1 :
  f (f 0 ^ 2) = 0 :=
begin
  have h := feq 0 0,
  rwa [add_zero, mul_zero, add_left_eq_self, ← sq] at h,
end

lemma fn_lem3_2 :
  f ≠ 0 → ∀ x : F, f x = 0 → x = 1 :=
begin
  intros h x h0,
  by_contra h1,
  apply h,
  apply fn_thm2 feq,
  use x; split; assumption,
end

lemma fn_lem3_3 :
  f ≠ 0 → f 0 ^ 2 = 1 :=
begin
  intros h,
  apply fn_lem3_2 feq h,
  exact fn_lem3_1 feq,
end

lemma fn_lem3_4 :
  f 1 = 0 :=
begin
  by_cases h : f = 0,
  rw [h, pi.zero_apply],
  have h0 := fn_lem3_1 feq,
  rwa fn_lem3_3 feq h at h0,
end

theorem fn_thm3 :
  f ≠ 0 → ∀ x : F, f x = 0 ↔ x = 1 :=
begin
  intros h x,
  split,
  exact fn_lem3_2 feq h x,
  intros h0; subst h0,
  exact fn_lem3_4 feq,
end



---- If f is injective, we are done; plus some auxiliary lemmas
lemma fn_lem4_1 :
  f 0 = 1 → ∀ x : F, f (x + 1) = f x - 1 :=
begin
  intros h x,
  have h0 := feq x 1,
  rw [fn_lem3_4 feq, mul_zero, mul_one, h] at h0,
  rw [← h0, add_sub_cancel'],
end

lemma fn_lem4_2 :
  f 0 = 1 → ∀ x : F, f (f x) + f x = 1 :=
begin
  intros h x,
  have h0 := feq x 0,
  rwa [mul_zero, h, mul_one, add_zero] at h0,
end

theorem fn_thm4 :
  f 0 = 1 → injective f → f = 1 - id :=
begin
  intros h h0,
  apply funext; intros x,
  have h1 := fn_lem4_2 feq h x,
  have h2 := fn_lem4_2 feq h (f x),
  rw [add_comm, ← h1, add_right_inj] at h2,
  rwa [pi.sub_apply, pi.one_apply, id.def, ← h1, h0 h2, add_sub_cancel'],
end



end general







end IMO2017A6
