import algebra.ring.basic tactic.ring

/-!
# IMO 2011 A3, Generalized Version

Let R be a non-trivial domain such that 2 has an inverse in R.
Determine all pairs of (f, g) functions R → R such that, for all x, y ∈ R,
  g(f(x + y)) = f(x) + (2x + y) g(y).

## Answer

(f, g) = (0, 0) and (f, g) = (x ↦ x² + C, id) for some C ∈ R.

## Solution

See https://www.imo-official.org/problems/IMO2011SL.pdf.
We will follow the official Solution.
It adopts directly to any domain R with 2 being invertible.

# Notes

1. The non-triviality is actually not required, but the trivial ring case is trivial.
2. It seems that the case char(R) = 2 is too ugly to even consider, let alone the general case.
-/

open function

namespace IMOSL
namespace IMO2011A3

variables {R : Type*} [comm_ring R] [is_domain R] [nontrivial R]

def fn_eq (f g : R → R) := ∀ x y : R, g (f (x + y)) = f x + (2 * x + y) * g y



namespace extra

/-- Ravi substitution -/
lemma ravi_subst (exists_inv_2 : ∃ t : R, 2 * t = 1) (x y z : R) :
  ∃ a b c : R, x = b + c ∧ y = c + a ∧ z = a + b :=
begin
  cases exists_inv_2 with t h,
  use [(y + z - x) * t, (z + x - y) * t, (x + y - z) * t],
  repeat { split }; ring_nf; rw [h, one_mul]
end

/-- A criterion for a quadratic polynomial to be zero -/
lemma poly_deg_2_zero (two_ne_zero : (2 : R) ≠ 0)
    {A B C : R} (h : ∀ x : R, A * x ^ 2 + B * x + C = 0) :
  A = 0 ∧ B = 0 ∧ C = 0 :=
begin
  have h0 : 2 * B = (A * 1 ^ 2 + B * 1 + C) - (A * (-1) ^ 2 + B * (-1) + C) := by ring,
  rw [h, h, sub_zero, mul_eq_zero, or_iff_right two_ne_zero] at h0,
  have h1 := h 0,
  rw [sq, mul_zero, mul_zero, zero_add, mul_zero, zero_add] at h1,
  have h2 := h 1,
  rw [h0, zero_mul, add_zero, h1, add_zero, one_pow, mul_one] at h2,
  repeat { split }; assumption
end

end extra



namespace results

variables {f g : R → R} (feq : fn_eq f g)
include feq

lemma fn_lem1 : ∀ x : R, g (f x) = f (-x) :=
begin
  intros x,
  have h := feq (-x) (2 * x),
  ring_nf at h; exact h
end

lemma fn_lem2 : ∀ a b : R, f (-a) - f (-b) = (a - b) * g (a + b) :=
begin
  intros a b,
  have h := feq (-b) (b + a),
  rw [← add_assoc, neg_add_self, zero_add, fn_lem1 feq, ← sub_eq_iff_eq_add'] at h,
  rw [h, two_mul, ← add_assoc, neg_add_cancel_comm, add_comm, ← sub_eq_add_neg, add_comm]
end

lemma fn_lem3 (exists_inv_2 : ∃ t : R, 2 * t = 1) :
  ∃ A B : R, ∀ x : R, g x = A * x + B :=
begin
  use [g 1 - g 0, g 0]; intros x,
  rcases extra.ravi_subst exists_inv_2 0 x 1 with ⟨a, b, c, h, rfl, h0⟩,
  rw [eq_comm, add_eq_zero_iff_eq_neg] at h; subst h,
  calc g (c + a) = (a - c) * g (a + c) : by rw [sub_eq_add_neg, ← h0, one_mul, add_comm]
  ... = f (-a) - f (- -c) + (f (- -c) - f (-c)) : by rw [← fn_lem2 feq, ← sub_add_sub_cancel]
  ... = (a + c) * g 1 + (f (- -c) - f (-c)) : by rw [fn_lem2 feq, ← h0, sub_neg_eq_add]
  ... = (a + c) * g 1 + (-c - c) * g 0 : by rw [fn_lem2 feq, neg_add_self]
  ... = (a + c) * (g 1 - g 0) + (a + c) * g 0 + (-c - c) * g 0 : by rw [mul_sub, sub_add_cancel]
  ... = (a + c) * (g 1 - g 0) + (a + -c) * g 0 : by rw [add_assoc, ← add_mul, add_add_sub_cancel]
  ... = (g 1 - g 0) * (c + a) + g 0 : by rw [← h0, one_mul, add_comm a c, mul_comm]
end

lemma fn_lem4 {A B : R} (h : ∀ x : R, g x = A * x + B) (x : R) :
  f x = A * x ^ 2 - B * x + f 0 :=
begin
  have h0 := fn_lem2 feq (-x) 0,
  rwa [neg_neg, neg_zero, sub_zero, add_zero, sub_eq_iff_eq_add, h] at h0,
  rw [h0, mul_comm, add_mul, mul_assoc, ← sq, neg_sq, mul_neg, sub_eq_add_neg]
end

lemma fn_lem5 {A B : R} (h : ∀ x : R, g x = A * x + B) (x : R) :
  (A ^ 2 - A) * x ^ 2 + -(A + 1) * B * x + (A * f 0 + B - f 0) = 0 :=
begin
  have h0 := fn_lem1 feq x,
  rw [h, fn_lem4 feq h x, fn_lem4 feq h (-x), ← sub_eq_zero] at h0,
  nth_rewrite 2 ← h0; ring
end

lemma fn_lem6 (two_ne_zero : (2 : R) ≠ 0) {A B : R} (h : ∀ x : R, g x = A * x + B) :
  B = 0 ∧ (A = 1 ∨ (A = 0 ∧ f 0 = 0)) :=
begin
  rcases extra.poly_deg_2_zero two_ne_zero (fn_lem5 feq h) with ⟨h0, h1, h2⟩,
  rw [sq, ← sub_one_mul, mul_eq_zero, sub_eq_zero] at h0,
  rcases h0 with rfl | rfl,
  { rw [one_mul, add_comm, add_sub_cancel] at h2,
    rw and_iff_right h2,
    left; refl },
  { rw [zero_add, neg_one_mul, neg_eq_zero] at h1,
    rw [zero_mul, zero_add, h1, zero_sub, neg_eq_zero] at h2,
    rw [and_iff_right h1, and_iff_left h2],
    right; refl }
end

end results



/-- Final solution -/
theorem final_solution_general (exists_inv_2 : ∃ t : R, 2 * t = 1) (f g : R → R) :
  fn_eq f g ↔ (f = 0 ∧ g = 0) ∨ ((∃ C : R, f = λ x, x ^ 2 + C) ∧ g = id) :=
begin
  split,
  { intros feq,
    rcases results.fn_lem3 feq exists_inv_2 with ⟨A, B, h⟩,
    replace exists_inv_2 : (2 : R) ≠ 0,
    { intros h0,
      cases exists_inv_2 with t X,
      rw [h0, zero_mul, eq_comm] at X,
      exact one_ne_zero X },
    rcases results.fn_lem6 feq exists_inv_2 h with ⟨rfl, rfl | ⟨rfl, h0⟩⟩,
    { right; rw and_comm; split,
      funext; rw [h, add_zero, one_mul, id.def],
      use f 0; funext; rw [results.fn_lem4 feq h, zero_mul, sub_zero, one_mul] },
    { left; split; funext,
      rw [results.fn_lem4 feq h, zero_mul, zero_mul, sub_zero, zero_add, h0, pi.zero_apply],
      rw [h, zero_mul, add_zero, pi.zero_apply] } },
  { rintros (⟨rfl, rfl⟩ | ⟨⟨C, rfl⟩, rfl⟩) x y; simp,
    ring }
end

end IMO2011A3
end IMOSL
