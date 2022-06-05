import
  algebra.algebra.basic
  logic.function.basic

/-
  IMO 2017 A6 (P2), Generalized Version
  Let F be an arbitrary field.
  Determine all functions f : F → F such that, for all x, y ∈ F,
          f(f(x) f(y)) + f(x + y) = f(xy).
          
  Note:
  1. Case F = ℝ is IMO 2017 A6.
  2. The case char F ≠ 2 is solved in the file A6_char_ne_2.lean
  2. The case char F = 2 is still open.
-/

namespace IMO2017A6

universe u
variable F : Type u
variable [field F]

open function
local attribute classical.prop_decidable



def fn_eq (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y)







namespace results

variable f : F → F

---- Show that f satisfies the equation iff -f also satisfies the equation
theorem fn_thm1 (feq : fn_eq F f) : fn_eq F (-f) :=
begin
  intros x y; simp,
  rwa [← (feq x y), neg_add],
end



---- Show that either f x = 0 → x = 1 or ∀ x, f x = 0
lemma fn_lem2_1 (feq : fn_eq F f) : (∃ x : F, x ≠ 1 ∧ f x = 0) → f 0 = 0 :=
begin
  intros h,
  rcases h with ⟨c, h, h0⟩,
  let d := c / (c - 1),
  have h1 := feq c d,
  suffices : (c + d = c * d),
  { rwa [this, add_left_eq_self, h0, zero_mul] at h1, },
  calc c + c / (c - 1) = (c * (c - 1) + c) / (c - 1) : _
  ... = (c * (c - 1) + c * 1) / (c - 1) : by rw mul_one
  ... = c * (c - 1 + 1) / (c - 1) : by rw ← mul_add
  ... = c * c / (c - 1) : by rw sub_add_cancel
  ... = c * (c / (c - 1)) : by rw mul_div_assoc,
  { rw add_div_eq_mul_add_div,
    rwa sub_ne_zero, },
end

lemma fn_lem2_2 (feq : fn_eq F f) : f 0 = 0 → f = 0 :=
begin
  intros h,
  apply funext; intros x,
  have h0 := feq x 0,
  rwa [h, mul_zero, mul_zero, add_zero, h, zero_add] at h0,
end

theorem fn_thm2 (feq : fn_eq F f) : (∃ x : F, x ≠ 1 ∧ f x = 0) → f = 0 :=
begin
  intros h,
  apply fn_lem2_2 F f feq,
  exact fn_lem2_1 F f feq h,
end



---- Now assume that f ≠ 0. Show that f x = 0 ↔ x = 1
lemma fn_lem3_1 (feq : fn_eq F f) : f (f 0 ^ 2) = 0 :=
begin
  have h := feq 0 0,
  rwa [add_zero, mul_zero, add_left_eq_self, ← sq] at h,
end

lemma fn_lem3_2 (feq : fn_eq F f) : f ≠ 0 → ∀ x : F, f x = 0 → x = 1 :=
begin
  intros h x h0,
  by_cases h1 : (x = 1),
  { exact h1, },
  { exfalso,
    apply h,
    apply fn_thm2 F f feq,
    use x,
    split; assumption, },
end

lemma fn_lem3_3 (feq : fn_eq F f) : f ≠ 0 → f 0 ^ 2 = 1 :=
begin
  intros h,
  apply fn_lem3_2 F f feq h,
  exact fn_lem3_1 F f feq,
end

lemma fn_lem3_4 (feq : fn_eq F f) : f 1 = 0 :=
begin
  by_cases h : f ≠ 0,
  { have h0 := fn_lem3_1 F f feq,
    rwa fn_lem3_3 F f feq h at h0, },
  { rw not_not at h,
    rw h,
    simp, },
end

theorem fn_thm3 (feq : fn_eq F f) : f ≠ 0 → ∀ x : F, f x = 0 ↔ x = 1 :=
begin
  intros h x,
  split,
  { exact fn_lem3_2 F f feq h x, },
  { intros h0; subst h0,
    exact fn_lem3_4 F f feq, },
end



---- If f is injective, we are done; plus some auxiliary lemmas
lemma fn_lem4_1 (feq : fn_eq F f) : f 0 = 1 → ∀ x : F, f (x + 1) = f x - 1 :=
begin
  intros h x,
  have h0 := feq x 1,
  rw [fn_lem3_4 F f feq, mul_zero, mul_one, h] at h0,
  rw [← h0, add_sub_cancel'],
end

lemma fn_lem4_2 (feq : fn_eq F f) : f 0 = 1 → ∀ x : F, f (f x) + f x = 1 :=
begin
  intros h x,
  have h0 := feq x 0,
  rwa [mul_zero, h, mul_one, add_zero] at h0,
end

theorem fn_thm4 (feq : fn_eq F f) : f 0 = 1 → injective f → f = 1 - id :=
begin
  intros h h0,
  apply funext; simp,
  intros x,
  have h1 := fn_lem4_2 F f feq h x,
  have h2 := fn_lem4_2 F f feq h (f x),
  rw [add_comm, ← h1, add_right_inj] at h2,
  rwa [← h1, h0 h2, add_sub_cancel'],
end

end results







end IMO2017A6
