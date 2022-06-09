import
  data.real.basic
  data.set.basic

/-
  IMO 2010 A1 (P1)
  Determine all functions f : ℝ → ℝ such that f(⌊x⌋ y) = f(x) ⌊f(y)⌋ for all x, y ∈ ℝ.

  Answer: f = 0 or f = C for some C ∈ [1, 2).

  See https://www.imo-official.org/problems/IMO2010SL.pdf.
  We will follow some parts of the Solution 1.
  For Case 2, where f(0) = 0, it is sufficient to prove that f(1/2) = 0 and then f(1) = 0 to get f = 0.
-/

namespace IMO2010A1

open function

def fn_eq (f : ℝ → ℝ) := ∀ x y : ℝ, f (⌊x⌋ * y) = f x * ⌊f y⌋



---- All functions satisying fn_eq are described here
namespace answer

lemma fn_answer1 :
  fn_eq 0 :=
begin
  intros _ _; simp,
end

lemma fn_answer2 (C : ℝ) :
  ⌊C⌋ = 1 → fn_eq (const ℝ C) :=
begin
  intros h _ _; simp,
  rw h; simp,
end

theorem fn_answer (f : ℝ → ℝ) :
  (∃ C : ℝ, (C = 0 ∨ ⌊C⌋ = 1) ∧ const ℝ C = f) → fn_eq f :=
begin
  intros h,
  rcases h with ⟨C, h | h, h0⟩,
  { rw [← h0, h],
    exact fn_answer1, },
  { rw ← h0,
    exact fn_answer2 C h, },
end

end answer



---- We prove that there are no other functions satisfying fn_eq here
namespace solution

variable f : ℝ → ℝ
variable feq : fn_eq f
include feq

lemma fn_lem1 :
  f 0 ≠ 0 → ∀ y : ℝ, ⌊f y⌋ = 1 :=
begin
  intros h y,
  have h0 := feq 0 y,
  simp at h0,
  rw [← div_left_inj' h, div_self h, mul_div_cancel_left _ h] at h0,
  have h1 : (↑⌊f y⌋ = ((1 : ℤ) : ℝ)),
  { rw ← h0; simp, },
  rw int.cast_inj at h1,
  exact h1,
end

lemma fn_lem2 :
  f 0 ≠ 0 → ∃ C : ℝ, ⌊C⌋ = 1 ∧ f = const ℝ C :=
begin
  intros h,
  have h0 := fn_lem1 f feq h 0,
  use f 0; split,
  exact h0,
  apply funext; intros x; simp,
  have h1 := feq x 0,
  rw h0 at h1,
  simp at h1,
  rwa h1,
end

lemma fn_lem3 :
  f 0 = 0 → f 2⁻¹ = 0 :=
begin
  intros h,
  have h0 : f 2⁻¹ * ⌊f 2⁻¹⌋ = 0,
  { rw ← feq,
    calc f (↑⌊(2 : ℝ)⁻¹⌋ * (2 : ℝ)⁻¹) = f 0 : _
    ... = 0 : by rw h,
    { apply congr_arg,
      norm_num,
      rw int.floor_eq_iff,
      norm_num, }, },
  rw mul_eq_zero at h0,
  cases h0 with h0 h0,
  { exact h0, },
  { have h1 := feq 1 2⁻¹,
    rw h0 at h1,
    simp at h1,
    exact h1, },
end

lemma fn_lem4 :
  f 0 = 0 → f 1 = 0 :=
begin
  intros h,
  have h0 := feq 2 2⁻¹,
  rw fn_lem3 f feq h at h0,
  have h1 : ⌊(2 : ℝ)⌋ = 2,
  { rw int.floor_eq_iff,
    norm_num, },
  rw h1 at h0,
  simp at h0,
  exact h0,
end

lemma fn_lem5 :
  f 0 = 0 → f = 0 :=
begin
  intros h,
  apply funext,
  intros x,
  have h0 := feq 1 x,
  rw fn_lem4 f feq h at h0,
  simp at h0,
  exact h0,
end

theorem fn_sol :
  ∃ C : ℝ, (C = 0 ∨ ⌊C⌋ = 1) ∧ const ℝ C = f :=
begin
  by_cases h : (f 0 = 0),
  { use 0; split,
    left; refl,
    rw fn_lem5 f feq h; simp, },
  { have h0 := fn_lem2 f feq h,
    rcases h0 with ⟨C, h0, h1⟩,
    use C; split,
    { right; exact h0, },
    { rwa h1, }, },
end

end solution



---- Wrapper
theorem IMO2010A1_sol :
  set_of fn_eq = const ℝ '' ({0} ∪ set.Ico 1 2) :=
begin
  have X : set.Ico 1 2 = {C : ℝ | ⌊C⌋ = 1},
  { rw set.ext_iff; simp,
    intros x,
    rw int.floor_eq_iff,
    have h : ↑(1 : ℤ) = (1 : ℝ) := by simp,
    rw h; refl, },
  rw [X, set.ext_iff]; simp,
  intros f; split,
  { exact solution.fn_sol f, },
  { exact answer.fn_answer f, },
end







end IMO2010A1
