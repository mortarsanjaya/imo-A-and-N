import
  data.real.basic
  data.set.basic

namespace IMO2010A1

/--
  IMO 2010 A1 (P1)

  Determine all functions f : ℝ → ℝ such that, for all x, y ∈ ℝ,
          f(⌊x⌋ y) = f(x) ⌊f(y)⌋.

  Answer: f = 0 or f = C for some C ∈ [1, 2).

  See https://www.imo-official.org/problems/IMO2010SL.pdf.
  We will follow some parts of the Solution 1.
  For Case 2 : f(0) = 0, we do the following steps instead:
  1. For any x ∈ [0, 1), we prove ⌊f(x)⌋ = 0 via proving f(x) ⌊f(x)⌋ = 0.
  2. Using f(1/2) = 0, prove that f(1) = 0.
  3. Using f(1) = 0, prove that f = 0.
-/
def fn_eq (f : ℝ → ℝ) :=
  ∀ x y : ℝ, f (⌊x⌋ * y) = f x * ⌊f y⌋






open function
open_locale classical

namespace results



---- All functions satisying fn_eq are described here
section answer

theorem fn_ans1 :
  fn_eq 0 :=
begin
  intros x y,
  rw [pi.zero_apply, pi.zero_apply, zero_mul],
end

theorem fn_ans2 (C : ℝ) (h : ⌊C⌋ = 1) :
  fn_eq (const ℝ C) :=
begin
  intros x y,
  rw [const_apply, h, int.cast_one, mul_one],
end

end answer



---- We prove that there are no other functions satisfying fn_eq here
section solution

variable {f : ℝ → ℝ}
variable feq : fn_eq f
include feq

lemma fn_lem1 :
  f 0 ≠ 0 → ∀ y : ℝ, ⌊f y⌋ = 1 :=
begin
  intros h y,
  have h0 := feq 0 y,
  rw [int.floor_zero, int.cast_zero, zero_mul, eq_comm, mul_right_eq_self₀] at h0,
  cases h0 with h0 h0,
  rwa [← int.cast_one, int.cast_inj] at h0,
  exfalso; exact h h0,
end

lemma fn_lem2 :
  f 0 ≠ 0 → ∃ C : ℝ, ⌊C⌋ = 1 ∧ const ℝ C = f :=
begin
  intros h,
  use f 0; split,
  exact fn_lem1 feq h 0,
  apply funext; intros x,
  have h1 := feq x 0,
  rwa [mul_zero, fn_lem1 feq h 0, int.cast_one, mul_one] at h1,
end

lemma fn_lem3 :
  f 0 = 0 → ∀ x : ℝ, ⌊x⌋ = 0 → ⌊f x⌋ = 0 :=
begin
  intros h x h0,
  have h1 := feq x x,
  rw [h0, int.cast_zero, zero_mul, h, zero_eq_mul] at h1,
  cases h1 with h1 h1,
  rw [h1, int.floor_zero],
  rwa [← int.cast_zero, int.cast_inj] at h1,
end

lemma fn_lem4 :
  f 0 = 0 → f 1 = 0 :=
begin
  intros h,
  have h0 := feq ↑(2 : ℤ) 2⁻¹,
  rwa [int.floor_coe, int.cast_bit0, int.cast_one, fn_lem3 feq h,
       int.cast_zero, mul_zero, mul_inv_cancel] at h0,
  exact two_ne_zero,
  rw [int.floor_eq_iff, int.cast_zero, zero_add],
  norm_num,
end

lemma fn_lem5 :
  f 0 = 0 → f = 0 :=
begin
  intros h,
  apply funext; intros x,
  have h0 := feq 1 x,
  rwa [fn_lem4 feq h, zero_mul, int.floor_one, int.cast_one, one_mul] at h0,
end

end solution



end results







---- Final solution
theorem final_solution :
  set_of fn_eq = {0} ∪ const ℝ '' (set.Ico 1 2) :=
begin
  have X : set.Ico (1 : ℝ) (2 : ℝ) = int.floor ⁻¹' {1} :=
    by rw [int.preimage_floor_singleton, int.cast_one]; refl,
  rw [X, eq_comm, set.ext_iff]; intros f,
  simp only [set.mem_set_of_eq, set.singleton_union, set.mem_insert_iff,
             set.mem_image, set.mem_preimage, set.mem_singleton_iff],
  split; intros h,

  ---- All functions on the RHS satisfy fn_eq
  { rcases h with h | ⟨C, h, h0⟩,
    rw h; exact results.fn_ans1,
    rw ← h0; refine results.fn_ans2 C h },
  
  ---- All functions satisfying fn_eq are in the RHS set
  { by_cases h0 : f 0 = 0,
    left; exact results.fn_lem5 h h0,
    right; exact results.fn_lem2 h h0 },
end

end IMO2010A1
