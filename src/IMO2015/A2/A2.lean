import data.int.basic

namespace IMOSL
namespace IMO2015A2

/--
  IMO 2015 A2

  Determine all functions f : ℤ → ℤ such that, for all x, y ∈ ℤ,
          f(x - f(y)) = f(f(x)) - f(y) - 1.

  Answer: f = -1 and f = x ↦ x + 1.

  See http://www.imo-official.org/problems/IMO2015SL.pdf
  We will follow the official Solution 1.
-/
def fn_eq (f : ℤ → ℤ) := ∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1



namespace extra

/-- Deduce linearity from f(x + 1) - f(x) being constant -/
lemma fn_linear_diff {f : ℤ → ℤ} {c : ℤ} (h : ∀ x : ℤ, f (x + 1) = f x + c) :
  ∀ x : ℤ, f x = c * x + f 0 :=
begin
  suffices : ∀ (x : ℤ) (n : ℕ), f (x + ↑n) = f x + c * ↑n,
  { intros x,
    rcases int.eq_coe_or_neg x with ⟨n, rfl | rfl⟩,
    rw [add_comm, ← this, zero_add],
    rw [add_comm, mul_neg, eq_add_neg_iff_add_eq, ← this, neg_add_self] },
  intros x n,
  induction n with n n_ih,
  rw [int.coe_nat_zero, mul_zero, add_zero, add_zero],
  rw [int.coe_nat_succ, ← add_assoc, h, n_ih, mul_add_one, add_assoc]
end

/-- A criterion for two linear polynomials to be equal -/
lemma linear_eq_match {a b c d : ℤ} (h : ∀ x : ℤ, a * x + b = c * x + d) :
  a = c ∧ b = d :=
begin
  have h0 := h 0,
  rw [mul_zero, mul_zero, zero_add, zero_add] at h0,
  split,
  have h1 := h 1,
  rwa [mul_one, mul_one, h0, add_left_inj] at h1,
  exact h0,
end

end extra



namespace results

variables {f : ℤ → ℤ} (feq : fn_eq f)
include feq

lemma fn_lem1 (x : ℤ) : f (f x) = f (x + 1) :=
begin
  have h := feq 0 (f 0),
  rw [zero_sub, sub_self, zero_sub] at h,
  have h0 := feq x (-f (f 0)),
  rwa [h, sub_neg_eq_add, sub_neg_eq_add, add_sub_cancel, eq_comm] at h0,
end

lemma fn_lem2 : ∀ x : ℤ, f x = (f (-1) + 1) * x + f 0 :=
begin
  have step1 : ∀ x y : ℤ, f (x - f y) = f (x + 1) - f y - 1 :=
    λ x y, by rw ← fn_lem1 feq; exact feq x y,
  apply extra.fn_linear_diff; intros x,
  rw [add_comm (f x), ← sub_eq_iff_eq_add, ← sub_add_cancel (f _ - _) (1 : ℤ),
      ← step1, ← sub_add_cancel (x - f x) 1, ← fn_lem1 feq, sub_right_comm,
      step1, sub_add_cancel, sub_self, zero_sub]
end

end results



/-- Final solution -/
theorem final_solution (f : ℤ → ℤ) :
  fn_eq f ↔ f = -1 ∨ f = (+ 1) :=
begin
  split,
  { intros feq,
    let A := f (-1) + 1,
    let B := f 0,
    have h : ∀ x : ℤ, f x = A * x + B := results.fn_lem2 feq,
    have h0 : A = A * A ∧ A + B = A * B + B :=
    begin
      apply extra.linear_eq_match; intros x,
      calc A * x + (A + B) = A * (x + 1) + B : by rw [mul_add, mul_one, add_assoc _ A]
      ... = A * (A * x + B) + B : by rw [← h, ← results.fn_lem1 feq, h, h]
      ... = A * A * x + (A * B + B) : by rw [mul_add, add_assoc, ← mul_assoc]
    end,
    cases h0 with h0 h1,
    rw [eq_comm, mul_left_eq_self₀] at h0,
    cases h0 with h0 h0,
    { right; ext x,
      rw [add_left_inj, h0, one_mul] at h1,
      rw [h, h0, one_mul, ← h1] },
    { left; ext x,
      rw [h, h0, zero_mul, zero_add],
      have h1 : f (-1) + 1 = 0 := h0,
      rwa [h, h0, zero_mul, zero_add, ← sub_neg_eq_add, sub_eq_zero] at h1 } },
  { rintros (rfl | rfl); intros x y; simp,
    rw [← sub_sub, sub_add_cancel, sub_sub, add_sub_add_right_eq_sub] },
end

end IMO2015A2
end IMOSL
