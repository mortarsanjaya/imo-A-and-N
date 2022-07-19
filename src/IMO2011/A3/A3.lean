import algebra.ring.basic ring_theory.non_zero_divisors tactic.ring

/-! # IMO 2011 A3, Generalized Version -/

open function
open_locale non_zero_divisors

namespace IMOSL
namespace IMO2011A3

def fn_eq {R : Type*} [ring R] (f g : R → R) := ∀ x y : R, g (f (x + y)) = f x + (2 * x + y) * g y



namespace extra

/-- A criterion for a quadratic polynomial to be zero over a ring with invertible 2 -/
lemma poly_deg_2_zero {R : Type*} [comm_ring R] (R2nzd : (2 : R) ∈ R⁰)
    {A B C : R} (h : ∀ x : R, A * x ^ 2 + B * x + C = 0) :
  A = 0 ∧ B = 0 ∧ C = 0 :=
begin
  have h0 := h 0,
  rw [sq, mul_zero, ← add_mul, mul_zero, zero_add] at h0,
  rw [← and_assoc, and_iff_left h0],
  conv at h { find (_ = _) { rw [h0, add_zero] } },
  replace h0 := h (-1),
  rw [neg_pow_bit0, one_pow, mul_one, mul_neg_one, add_neg_eq_zero] at h0,
  rw [h0, and_self],
  replace h1 := h 1,
  rwa [one_pow, mul_one, mul_one, h0, ← two_mul,
       mul_left_mem_non_zero_divisors_eq_zero_iff R2nzd] at h1
end

end extra



section results

variables {R : Type*} [comm_ring R]

private lemma lem1_1 {f g : R → R} (feq : fn_eq f g) :
    ∀ x y : R, f x - f y = (2 * y + x) * g x - (2 * x + y) * g y :=
  λ x y, by rw [sub_eq_sub_iff_add_eq_add, ← feq, add_comm, feq, add_comm]

private lemma lem1_2 (R2nzd : (2 : R) ∈ R⁰) {f g : R → R} (feq : fn_eq f g) :
  ∃ A B : R, ∀ x : R, g x = A * x + B :=
begin
  use [g 1 - g 0, g 0]; intros x,
  have h := congr_arg2 (λ x y, x + y) (lem1_1 feq x 1) (lem1_1 feq 0 x),
  simp only [] at h; rw [sub_add_sub_cancel', lem1_1 feq] at h,
  simp only [add_zero, mul_one, zero_add, mul_zero, one_mul] at h,
  rwa [sub_add_sub_comm, add_comm, add_mul, ← add_assoc, add_sub_add_right_eq_sub, add_one_mul,
       sub_eq_iff_eq_add, ← sub_sub, sub_add_cancel, mul_assoc, mul_assoc, ← mul_add, ← mul_sub,
       mul_cancel_left_mem_non_zero_divisor R2nzd, eq_sub_iff_add_eq, add_comm _ (g x),
       ← sub_eq_iff_eq_add, add_sub_assoc, ← mul_sub, add_comm, mul_comm, eq_comm] at h
end

private lemma lem2_1 {f g : R → R} (feq : fn_eq f g) {A B : R} (h : ∀ x : R, g x = A * x + B) :
  ∀ x : R, f x = A * x ^ 2 - B * x + f 0 :=
begin
  intros x,
  have h0 := lem1_1 feq x 0,
  rwa [mul_zero, zero_add, add_zero, h, mul_comm, add_mul, mul_assoc, ← sq, h, mul_zero, zero_add,
       mul_right_comm, mul_assoc, two_mul, add_sub_add_right_eq_sub, sub_eq_iff_eq_add] at h0
end

private lemma lem2_2 {f g : R → R} (feq : fn_eq f g) {A B : R} (h : ∀ x : R, g x = A * x + B) :
  ∀ x : R, A * (A - 1) * x ^ 2 + -(A + 1) * B * x + (f 0 * (A - 1) + B) = 0 :=
begin
  intros x,
  have h0 := feq (-x) (2 * x),
  rw [← mul_add, neg_add_self, mul_zero, zero_mul, add_zero, two_mul,
      neg_add_cancel_left, h, lem2_1 feq h, lem2_1 feq h (-x), ← sub_eq_zero] at h0,
  nth_rewrite 1 ← h0; ring
end

private lemma lem2_3 (R2nzd : (2 : R) ∈ R⁰) {f g : R → R} (feq : fn_eq f g)
    {A B : R} (h : ∀ x : R, g x = A * x + B) :
  B = 0 ∧ A * (A - 1) = 0 ∧ f 0 * (A - 1) = 0 :=
begin
  rcases extra.poly_deg_2_zero R2nzd (lem2_2 feq h) with ⟨h0, h1, h2⟩,
  rw [add_eq_zero_iff_neg_eq] at h2,
  suffices : B = 0,
    rw [and_iff_right this, and_iff_right h0, ← neg_eq_zero, h2, this],
  rwa [← h2, neg_mul_neg, mul_left_comm, add_one_mul, h0, zero_add, ← neg_eq_zero, h2] at h1
end

end results



/-- Final solution -/
theorem final_solution_general {R : Type*} [comm_ring R] (R2nzd : (2 : R) ∈ R⁰) (f g : R → R) :
    fn_eq f g ↔ ∃ A C : R,
  (f = λ x, A * x ^ 2 + C) ∧ (g = λ x, A * x) ∧ A * (A - 1) = 0 ∧ f 0 * (A - 1) = 0 :=
begin
  split,
  { intros feq,
    rcases lem1_2 R2nzd feq with ⟨A, B, h⟩,
    rcases lem2_3 R2nzd feq h with ⟨rfl, h0, h1⟩,
    use [A, f 0]; rw [and_iff_left h1, and_iff_left h0]; split,
    funext x; rw [lem2_1 feq h, zero_mul, sub_zero],
    funext x; rw [h, add_zero] },
  { rintros ⟨A, C, rfl, rfl, h, h0⟩ x y,
    simp only [] at h0 ⊢,
    rw [zero_pow zero_lt_two, mul_zero, zero_add] at h0,
    rw [mul_sub_one, sub_eq_zero, mul_comm] at h h0,
    rw [mul_add, h0, ← mul_assoc, h],
    ring }
end

/-- Final solution when R is an integral domain -/
theorem final_solution_domain {R : Type*} [comm_ring R] [is_domain R] (R2nzd : (2 : R) ∈ R⁰)
  (f g : R → R) : fn_eq f g ↔ (f = 0 ∧ g = 0) ∨ ((∃ C : R, f = λ x, x ^ 2 + C) ∧ g = id) :=
begin
  rw final_solution_general R2nzd; split,
  { rintros ⟨A, C, rfl, rfl, h, h0⟩,
    rw [mul_eq_zero, sub_eq_zero] at h h0,
    rcases h with rfl | rfl,
    simp only [] at h0; rw [or_iff_left, zero_mul, zero_add] at h0,
    left; simp only [h0, zero_mul, zero_add],
    rw and_self; refl,
    exact zero_ne_one,
    clear h0; right; simp only [one_mul]; split,
    use C,
    refl },
  { rintros (⟨rfl, rfl⟩ | ⟨⟨C, rfl⟩, rfl⟩),
    use [0, 0]; simp only [zero_mul, pi.zero_apply, add_zero],
    rw [← and_assoc, and_self, and_self]; split; refl,
    use [1, C]; simp only [one_mul],
    rw [sub_self, mul_zero, and_self]; repeat { split } }
end

end IMO2011A3
end IMOSL
