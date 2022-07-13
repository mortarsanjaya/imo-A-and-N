import algebra.ring.basic tactic.ring

/-! # IMO 2011 A3, Generalized Version -/

open function

namespace IMOSL
namespace IMO2011A3

variables {R : Type*} [comm_ring R]

def fn_eq (f g : R → R) := ∀ x y : R, g (f (x + y)) = f x + (2 * x + y) * g y



namespace extra

/-- Ravi substitution -/
lemma ravi_subst [invertible (2 : R)] (x y z : R) :
  ∃ a b c : R, x = b + c ∧ y = c + a ∧ z = a + b :=
begin
  use [(y + z - x) * ⅟ 2, (z + x - y) *  ⅟ 2, (x + y - z) *  ⅟ 2],
  repeat { split }; ring_nf; rw [mul_inv_of_self, one_mul]
end

/-- A criterion for a quadratic polynomial to be zero over a ring with invertible 2 -/
lemma poly_deg_2_zero [invertible (2 : R)] {A B C : R} (h : ∀ x : R, A * x ^ 2 + B * x + C = 0) :
  A = 0 ∧ B = 0 ∧ C = 0 :=
begin
  have h0 : 2 * B = (A * 1 ^ 2 + B * 1 + C) - (A * (-1) ^ 2 + B * (-1) + C) := by ring,
  rw [h, h, sub_zero] at h0,
  replace h0 := congr_arg (λ x, ⅟ (2 : R) * x) h0,
  simp only [] at h0,
  rw [mul_zero, inv_of_mul_self_assoc] at h0,
  have h1 := h 0,
  rw [sq, mul_zero, mul_zero, zero_add, mul_zero, zero_add] at h1,
  have h2 := h 1,
  rw [h0, zero_mul, add_zero, h1, add_zero, one_pow, mul_one] at h2,
  repeat { split }; assumption
end

end extra



section results

variables {f g : R → R} (feq : fn_eq f g)
include feq

private lemma fn_lem1 : ∀ x : R, g (f x) = f (-x) :=
begin
  intros x,
  have h := feq (-x) (2 * x),
  ring_nf at h; exact h
end

private lemma fn_lem2 : ∀ a b : R, f (-a) - f (-b) = (a - b) * g (a + b) :=
begin
  intros a b,
  have h := feq (-b) (b + a),
  rw [← add_assoc, neg_add_self, zero_add, fn_lem1 feq, ← sub_eq_iff_eq_add'] at h,
  rw [h, two_mul, ← add_assoc, neg_add_cancel_comm, add_comm, ← sub_eq_add_neg, add_comm]
end

private lemma fn_lem3 [invertible (2 : R)] : ∃ A B : R, ∀ x : R, g x = A * x + B :=
begin
  use [g 1 - g 0, g 0]; intros x,
  rcases extra.ravi_subst 0 x 1 with ⟨a, b, c, h, rfl, h0⟩,
  rw [eq_comm, add_eq_zero_iff_eq_neg] at h; subst h,
  calc g (c + a) = (a - c) * g (a + c) : by rw [sub_eq_add_neg, ← h0, one_mul, add_comm]
  ... = f (-a) - f (- -c) + (f (- -c) - f (-c)) : by rw [← fn_lem2 feq, ← sub_add_sub_cancel]
  ... = (a + c) * g 1 + (f (- -c) - f (-c)) : by rw [fn_lem2 feq, ← h0, sub_neg_eq_add]
  ... = (a + c) * g 1 + (-c - c) * g 0 : by rw [fn_lem2 feq, neg_add_self]
  ... = (a + c) * (g 1 - g 0) + (a + c) * g 0 + (-c - c) * g 0 : by rw [mul_sub, sub_add_cancel]
  ... = (a + c) * (g 1 - g 0) + (a + -c) * g 0 : by rw [add_assoc, ← add_mul, add_add_sub_cancel]
  ... = (g 1 - g 0) * (c + a) + g 0 : by rw [← h0, one_mul, add_comm a c, mul_comm]
end

private lemma fn_lem4 {A B : R} (h : ∀ x : R, g x = A * x + B) (x : R) :
  f x = A * x ^ 2 - B * x + f 0 :=
begin
  have h0 := fn_lem2 feq (-x) 0,
  rwa [neg_neg, neg_zero, sub_zero, add_zero, sub_eq_iff_eq_add, h] at h0,
  rw [h0, mul_comm, add_mul, mul_assoc, ← sq, neg_sq, mul_neg, sub_eq_add_neg]
end

private lemma fn_lem5 {A B : R} (h : ∀ x : R, g x = A * x + B) (x : R) :
  A * (A - 1) * x ^ 2 + -(A + 1) * B * x + (f 0 * (A - 1) + B) = 0 :=
begin
  have h0 := fn_lem1 feq x,
  rw [h, fn_lem4 feq h x, fn_lem4 feq h (-x), ← sub_eq_zero] at h0,
  nth_rewrite 1 ← h0; ring
end

private lemma fn_lem6 [invertible (2 : R)] {A B : R} (h : ∀ x : R, g x = A * x + B) :
  B = 0 ∧ A * (A - 1) = 0 ∧ f 0 * (A - 1) = 0 :=
begin
  rcases extra.poly_deg_2_zero (fn_lem5 feq h) with ⟨h0, h1, h2⟩,
  rw [add_eq_zero_iff_neg_eq] at h2,
  suffices : B = 0,
    rw [and_iff_right this, and_iff_right h0, ← neg_eq_zero, h2, this],
  rwa [← h2, neg_mul_neg, mul_left_comm, add_one_mul, h0, zero_add, ← neg_eq_zero, h2] at h1
end

end results



/-- Final solution -/
theorem final_solution_general [invertible (2 : R)] (f g : R → R) : fn_eq f g ↔ ∃ A C : R,
  (f = λ x, A * x ^ 2 + C) ∧ (g = λ x, A * x) ∧ A * (A - 1) = 0 ∧ f 0 * (A - 1) = 0 :=
begin
  split,
  { intros feq,
    rcases fn_lem3 feq with ⟨A, B, h⟩,
    rcases fn_lem6 feq h with ⟨rfl, h0, h1⟩,
    use [A, f 0]; rw [and_iff_left h1, and_iff_left h0]; split,
    funext x; rw [fn_lem4 feq h, zero_mul, sub_zero],
    funext x; rw [h, add_zero] },
  { rintros ⟨A, C, rfl, rfl, h, h0⟩ x y,
    simp only [] at h0 ⊢,
    rw [zero_pow zero_lt_two, mul_zero, zero_add] at h0,
    rw [mul_sub_one, sub_eq_zero, mul_comm] at h h0,
    rw [mul_add, h0, ← mul_assoc, h],
    ring }
end

/-- Final solution when R is an integral domain -/
theorem final_solution_domain [is_domain R] [invertible (2 : R)] (f g : R → R) :
  fn_eq f g ↔ (f = 0 ∧ g = 0) ∨ ((∃ C : R, f = λ x, x ^ 2 + C) ∧ g = id) :=
begin
  rw final_solution_general; split,
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
