import data.int.basic data.pi.algebra

/-! # IMO 2015 A2 -/

namespace IMOSL
namespace IMO2015A2

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
lemma linear_eq_match {a b c d : ℤ} (h : ∀ x : ℤ, a * x + b = c * x + d) : a = c ∧ b = d :=
begin
  have h0 := h 0,
  rw [mul_zero, mul_zero, zero_add, zero_add] at h0,
  have h1 := h 1,
  rw [mul_one, mul_one, h0, add_left_inj] at h1,
  exact and.intro h1 h0
end

end extra



section results

variables {f : ℤ → ℤ} (feq : fn_eq f)
include feq

private lemma fn_lem1 (x : ℤ) : f (f x) = f (x + 1) :=
begin
  have h := feq 0 (f 0),
  rw [zero_sub, sub_self, zero_sub] at h,
  have h0 := feq x (-f (f 0)),
  rwa [h, sub_neg_eq_add, sub_neg_eq_add, add_sub_cancel, eq_comm] at h0
end

private lemma fn_lem2 : ∀ x : ℤ, f x = (f (-1) + 1) * x + f 0 :=
begin
  apply extra.fn_linear_diff; intros x,
  rw [add_comm (f x), ← sub_eq_iff_eq_add, ← sub_eq_iff_eq_add, ← fn_lem1 feq, ← feq,
      ← sub_add_cancel (x - f x) 1, ← fn_lem1 feq, sub_sub, add_comm, ← sub_sub, feq,
      fn_lem1 feq, sub_add_cancel, sub_self, zero_sub]
end

end results



/-- Final solution -/
theorem final_solution (f : ℤ → ℤ) :
  fn_eq f ↔ f = -1 ∨ f = (+ 1) :=
begin
  split,
  { intros feq,
    have h := fn_lem2 feq,
    cases eq_or_ne (f (-1) + 1) 0 with h0 h0,
    { simp only [h0, zero_mul, zero_add] at h,
      left; funext x,
      rw [h, ← h (-1), pi.neg_apply, pi.one_apply, ← add_eq_zero_iff_eq_neg, h0] },
    { right; funext x,
      have h1 := fn_lem1 feq x,
      rw [h, h (x + 1), add_left_inj] at h1,
      exact int.eq_of_mul_eq_mul_left h0 h1 } },
  { rintros (rfl | rfl) x y; simp,
    rw [← add_sub_right_comm, sub_sub] }
end

end IMO2015A2
end IMOSL
