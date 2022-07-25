import algebra.algebra.basic algebra.char_p.two ring_theory.non_zero_divisors

/-! # IMO 2015 A4 (P5), Generalized Version -/

open function
open_locale non_zero_divisors classical

namespace IMOSL
namespace IMO2015A4

variables {R : Type*} [ring R]

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
private theorem case_f0_ne_0 [no_zero_divisors R]
  {f : R → R} (feq1 : fn_eq1 f) (f0_ne_0 : f 0 ≠ 0) : f = λ x, 2 - 2 * x :=
begin
  funext x,
  have h := feq1 0 (f x + 2 * x - 1),
  rwa [zero_mul, zero_add, lem1_2 feq1, zero_add, mul_zero, zero_add,
      lem1_2 feq1, ← mul_sub_one, zero_eq_mul, or_iff_right f0_ne_0,
      sub_sub, sub_eq_zero, ← eq_sub_iff_add_eq] at h
end



section case_R2nzd

variables (R2nzd : (2 : R) ∈ R⁰) {f : R → R} (feq1 : fn_eq1 f) (f0_eq_0 : f 0 = 0)
include R2nzd feq1 f0_eq_0

private lemma lem2_1 : f 1 = 0 :=
begin
  have h := lem1_2 feq1 0,
  rw [f0_eq_0, zero_add, mul_zero, zero_sub] at h,
  have h0 := feq1 1 (-1),
  rw [add_neg_self, f0_eq_0, zero_add, two_mul, add_neg_cancel_right, one_mul, h, sub_zero,
       mul_neg_one, eq_neg_iff_add_eq_zero, ← mul_two] at h0,
  exact mem_non_zero_divisors_iff.mp R2nzd _ h0
end

private lemma lem2_2 (x : R) : f (f (1 + x) + 2 + x) = - f x :=
begin
  have h := feq1 1 x,
  rwa [one_mul, mul_one, lem2_1 R2nzd feq1 f0_eq_0, zero_mul, zero_sub] at h
end

private lemma lem2_3 (x : R) : f (f x + 2 * x + 1) = 0 :=
begin
  have lem2_1 := lem2_1 R2nzd feq1 f0_eq_0,
  have h := feq1 x 0,
  rw [add_zero, add_zero, mul_zero, mul_zero, f0_eq_0, sub_zero] at h,
  have h0 := feq1 1 (f x + 2 * x - 1),
  rwa [one_mul, lem1_2 feq1 x, sub_zero, lem2_1, zero_mul, add_comm (1 : R) _,
       sub_add_cancel, h, zero_add, two_mul, add_comm, sub_add_add_cancel] at h0
end

private lemma lem2_4 (x : R) : f (- x) = - (f x) :=
begin
  have h := lem2_3 R2nzd feq1 f0_eq_0 (x + -1),
  rw [mul_add, two_mul (-1 : R), add_assoc, add_assoc, neg_add_cancel_comm] at h,
  have h0 := feq1 x (-1),
  rwa [add_assoc, h, eq_comm, sub_eq_zero, mul_neg_one, mul_neg_one, eq_comm] at h0
end

/-- Case 2: f(0) = 0, 2 is not a (right) zero divisor in R -/
private theorem case_f0_eq_0_R2nzd : f = 0 :=
begin
  funext x,
  have lem2_4 := lem2_4 R2nzd feq1 f0_eq_0,
  have h := feq1 (-1) (-x),
  rwa [neg_mul_neg, one_mul, lem2_4, lem2_1 R2nzd feq1 f0_eq_0, neg_zero, zero_mul,
       zero_sub, ← neg_add, lem2_4, mul_neg_one, ← neg_add, ← neg_add, lem2_4,
       lem2_2 R2nzd feq1 f0_eq_0, neg_neg, eq_neg_iff_add_eq_zero, ← mul_two] at h,
  exact mem_non_zero_divisors_iff.mp R2nzd _ h
end

end case_R2nzd



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
private theorem case_f0_eq_0_char_eq_2 : f = 0 :=
begin
  funext x,
  have h := lem3_4 feq2 f0_eq_0 (x + 1),
  rw [lem3_3 feq2 f0_eq_0, lem3_4 feq2 f0_eq_0] at h,
  have h0 := lem3_3 feq2 f0_eq_0 x,
  rwa [← h, mul_add_one, add_right_eq_self] at h0
end

end case_char_eq_2

end results



/-- Final solution -/
theorem final_solution_domain [is_domain R] (f : R → R) : fn_eq f ↔ f = id ∨ f = λ x, 2 - x :=
begin
  split,
  { intros h,
    replace h := lem1_1 h,
    cases eq_or_ne ((f - id) 0) 0 with h0 h0,
    { left; rw ← sub_eq_zero,
      cases ne_or_eq (ring_char R) 2 with char_ne_2 char_eq_2,
      { refine case_f0_eq_0_R2nzd _ h h0,
        rw mem_non_zero_divisors_iff; intros x h,
        rwa [mul_eq_zero, or_iff_left] at h,
        rwa [bit0, add_eq_zero_iff_eq_neg, eq_comm, neg_one_eq_one_iff] },
      { rw ring_char.eq_iff at char_eq_2,
        resetI,
        simp only [fn_eq1, char_two.two_eq_zero, zero_mul, add_zero] at h,
        exact case_f0_eq_0_char_eq_2 h h0 } },
    { right; funext x,
      have h1 : (f - id) x = 2 - 2 * x := by rw case_f0_ne_0 h h0,
      rwa [pi.sub_apply, id.def, two_mul, ← sub_sub, sub_left_inj] at h1 } },
  { rintros (rfl | rfl) x y; simp only [id.def],
    rw [← add_sub_assoc x, add_sub_add_left_eq_sub, sub_sub_cancel, sub_mul, sub_add_sub_comm,
        add_sub_assoc, ← sub_sub, two_mul, add_sub_cancel, add_sub_left_comm] }
end

end IMO2015A4
end IMOSL
