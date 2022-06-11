import
  data.real.basic
  data.set.basic

namespace IMO2010A1

/--
  IMO 2010 A1 (P1)

  Determine all functions f : ℝ → ℝ such that, for all x, y ∈ ℝ,
          f(⌊x⌋ y) = f(x) ⌊f(y)⌋.

  Answer: f = 0 or f = C for some C ∈ [1, 2).

  Main theorem: IMO2010A1_sol

  See https://www.imo-official.org/problems/IMO2010SL.pdf.
  We will follow some parts of the Solution 1.
  For Case 2 : f(0) = 0, we do the following steps instead:
  1. For any x ∈ [0, 1), we prove f(x) = 0 via proving f(x) ⌊f(x)⌋ = 0.
  2. Using f(1/2) = 0, prove that f(1) = 0.
  3. Using f(1) = 0, prove that f = 0.
-/
def fn_eq (f : ℝ → ℝ) :=
  ∀ x y : ℝ, f (⌊x⌋ * y) = f x * ⌊f y⌋



open function







---- All functions satisying fn_eq are described here
namespace answer

theorem fn_ans (f : ℝ → ℝ) :
  (∃ C : ℝ, (C = 0 ∨ ⌊C⌋ = 1) ∧ const ℝ C = f) → fn_eq f :=
begin
  intros h _ _,
  rcases h with ⟨C, h | h, h0⟩,
  rw [← h0, const_apply, h, zero_mul],
  rw [← h0, const_apply, h, int.cast_one, mul_one],
end

end answer



---- We prove that there are no other functions satisfying fn_eq here
namespace solution

variable {f : ℝ → ℝ}
variable feq : fn_eq f
include feq

lemma fn_lem1 :
  f 0 ≠ 0 → ∀ y : ℝ, ⌊f y⌋ = 1 :=
begin
  intros h y,
  have h0 := feq 0 y,
  rwa [int.floor_zero, int.cast_zero, ← mul_one (f _), zero_mul,
       mul_right_inj' h, ← int.cast_one, int.cast_inj, eq_comm] at h0,
end

lemma fn_lem2 :
  f 0 ≠ 0 → ∃ C : ℝ, ⌊C⌋ = 1 ∧ const ℝ C = f :=
begin
  intros h,
  use f 0; split,
  exact fn_lem1 feq h 0,
  apply funext; intros x,
  have h1 := feq x 0,
  rwa [fn_lem1 feq h 0, mul_zero, int.cast_one, mul_one] at h1,
end

lemma fn_lem3 :
  f 0 = 0 → ∀ x : ℝ, ⌊x⌋ = 0 → f x = 0 :=
begin
  intros h x h0,
  have h1 := feq x x,
  rw [h0, int.cast_zero, zero_mul, h, zero_eq_mul] at h1,
  cases h1 with h1 h1,
  exact h1,
  have h2 := feq 1 x,
  rwa [h1, mul_zero, int.floor_one, int.cast_one, one_mul] at h2,
end

lemma fn_lem4 :
  f 0 = 0 → f 1 = 0 :=
begin
  intros h,
  have h0 := feq ↑(2 : ℤ) (↑(2 : ℤ))⁻¹,
  rwa [int.floor_coe, fn_lem3 feq h (↑(2 : ℤ))⁻¹, mul_inv_cancel,
      int.floor_zero, int.cast_zero, mul_zero] at h0,
  all_goals { simp only [int.cast_bit0, int.cast_one] },
  exact two_ne_zero,
  rw int.floor_eq_iff; norm_num,
end

lemma fn_lem5 :
  f 0 = 0 → f = 0 :=
begin
  intros h,
  apply funext; intros x,
  have h0 := feq 1 x,
  rwa [fn_lem4 feq h, zero_mul, int.floor_one, int.cast_one, one_mul] at h0,
end

theorem fn_sol :
  ∃ C : ℝ, (C = 0 ∨ ⌊C⌋ = 1) ∧ const ℝ C = f :=
begin
  by_cases h : f 0 = 0,
  { use 0; split,
    left; refl,
    rw [fn_lem5 feq h, pi.const_zero] },
  { rcases fn_lem2 feq h with ⟨C, h0, h1⟩,
    use C; split,
    right; exact h0,
    exact h1 },
end

end solution



---- Wrapper
theorem IMO2010A1_sol :
  set_of fn_eq = const ℝ '' ({0} ∪ set.Ico 1 2) :=
begin
  have X : set.Ico 1 2 = {C : ℝ | ⌊C⌋ = 1},
  { rw set.ext_iff; intros x,
    rw [set.mem_Ico, set.mem_set_of_eq, int.floor_eq_iff, int.cast_one],
    refl },
  rw [X, set.ext_iff]; intros f,
  rw [set.mem_set_of_eq, set.singleton_union, set.mem_image],
  split; intros h,
  exact solution.fn_sol h,
  exact answer.fn_ans f h,
end







end IMO2010A1
