import
  data.real.basic
  data.real.sqrt
  data.real.nnreal
  algebra.algebra.basic
  algebra.char_p.basic
  algebra.char_p.two
  data.polynomial.basic

/-! # IMO 2012 A5, Generalized Version -/

open function nnreal
open_locale nnreal classical

namespace IMOSL
namespace IMO2012A5

variables {R : Type*} [comm_ring R] [is_domain R]

def fn_eq (f : ℝ → R) := ∀ x y : ℝ, f (1 + x * y) - f(x + y) = f x * f y



namespace extra

/-- For any x ≤ 0, there exists u ∈ ℝ such that x = 1 + u - u^2 -/
lemma real_poly_range1 {x : ℝ} (h : x ≤ 0) : ∃ u : ℝ, x = 1 + u * (1 - u) :=
begin
  use [(real.sqrt (5 - 4 * x) + 1) / 2],
  field_simp; ring_nf,
  rw [real.sq_sqrt, neg_add, neg_neg, neg_add_cancel_right],
  linarith only [h] ---- Too lazy to explicitly write the steps
end

/-- For any u, v ≥ 0, there exists x, y ∈ ℝ such that u = (x - y)^2 and v = 4xy. -/
lemma real_mv_poly_range1 (u v : ℝ≥0) : ∃ x y : ℝ, (u : ℝ) = (x - y) ^ 2 ∧ (v : ℝ) = 4 * (x * y) :=
begin
  have h := nnreal.coe_nonneg u,
  use [(sqrt (u + v) + sqrt u) / 2, (sqrt (u + v) - sqrt u) / 2],
  split; field_simp; ring_nf,
  rw real.sq_sqrt h,
  rw [real.sq_sqrt (add_nonneg (nnreal.coe_nonneg v) h), real.sq_sqrt h, mul_add, add_sub_cancel]
end

lemma f_abs_eq_of_even {α} {f : ℝ → α} (h : ∀ x : ℝ, f (-x) = f x) (x : ℝ) : f (|x|) = f x :=
begin
  cases le_or_lt 0 x with h0 h0,
  rw ← abs_eq_self at h0; rw h0,
  replace h0 := le_of_lt h0,
  rw ← abs_eq_neg_self at h0; rw [h0, h]
end

lemma exists_eq_nnabs_sq (x : ℝ≥0) : ∃ u : ℝ≥0, x = u ^ 2 :=
  by use sqrt x; rw sq_sqrt



/--
  If R is a domain of characteristic non-zero, there is no ring hom ℝ → R.

  If possible, replace this and `nnreal_hom_empty` with `semifield_hom_empty`:
    For any semifield F of characteristic zero and nontrivial semiring R of
      characteristic non-zero, there is no semiring hom F → R.

  I will wait until ℝ≥0 has been given a semifield instance.
-/
instance real_hom_empty {p : ℕ} [fact (p ≠ 0)] [char_p R p] : is_empty (ℝ →+* R) :=
{ false := λ φ, begin
    have h := map_nat_cast φ p,
    rw char_p.cast_eq_zero R at h,
    replace h := mul_eq_zero_of_left h (φ p⁻¹),
    rw [← map_mul, mul_inv_cancel, map_one] at h,
    exact one_ne_zero h,
    rw nat.cast_ne_zero,
    exact fact.out (p ≠ 0)
  end }

instance nnreal_hom_empty {p : ℕ} [fact (p ≠ 0)] [char_p R p] : is_empty (ℝ≥0 →+* R) :=
{ false := λ φ, begin
    have h := map_nat_cast φ p,
    rw char_p.cast_eq_zero R at h,
    replace h := mul_eq_zero_of_left h (φ p⁻¹),
    rw [← map_mul, mul_inv_cancel, map_one] at h,
    exact one_ne_zero h,
    rw nat.cast_ne_zero,
    exact fact.out (p ≠ 0)
  end }

end extra



section results

variables {f : ℝ → R} (feq : fn_eq f)
include feq

private lemma lem1_1 : f 1 = 0 :=
begin
  have h := feq 1 1,
  rwa [mul_one, sub_self, zero_eq_mul_self] at h
end

private lemma lem1_2 (h : f 0 ≠ -1) : f = 0 :=
begin
  funext x,
  have h0 := feq x 0,
  rwa [mul_zero, add_zero, lem1_1 feq, zero_sub, add_zero, ← mul_neg_one,
       mul_eq_mul_left_iff, eq_comm, or_iff_right h] at h0
end

private lemma lem1_3 (x : ℝ) : f x - f (-x) = f (-1) * f (1 - x) :=
begin
  have h := feq (-1) (1 - x),
  rwa [neg_one_mul, neg_sub, add_sub_cancel'_right, ← add_sub_assoc, neg_add_self, zero_sub] at h
end



section case_fneg1_ne_0

variable (fneg1_ne_0 : f (-1) ≠ 0)
include fneg1_ne_0

private lemma lem2_1 : f 0 = -1 :=
  by contrapose! fneg1_ne_0 with f0_ne_neg1; rw [lem1_2 feq f0_ne_neg1, pi.zero_apply]

private lemma lem2_2 (x : ℝ) : f (2 - x) = -f x :=
begin
  have h := lem1_3 feq (-(1 - x)),
  rwa [neg_neg, ← neg_sub, lem1_3 feq (1 - x), ← mul_neg, mul_eq_mul_left_iff,
       or_iff_left fneg1_ne_0, sub_sub_cancel, sub_neg_eq_add, ← add_sub_assoc, eq_comm] at h
end

private lemma lem2_3 (x : ℝ) : f (x + 2) = f x + 2 :=
begin
  revert x; suffices : ∀ x : ℝ, x ≤ 0 → f (x + 2) - f x = f 3 - f 1,
  { have h := lem2_2 feq fneg1_ne_0 0,
    rw [sub_zero, lem2_1 feq fneg1_ne_0, neg_neg] at h,
    have h0 := this 0 (le_refl 0),
    rw [← h0, zero_add, h, lem2_1 feq fneg1_ne_0, sub_neg_eq_add, ← bit0] at this,
    clear h0; intros x,
    rw ← sub_eq_iff_eq_add',
    cases le_or_lt x 0 with h0 h0,
    exact this x h0,
    rw [← neg_sub, sub_eq_add_neg, ← lem2_2 feq fneg1_ne_0, ← sub_sub, sub_sub_cancel_left,
        neg_add, ← lem2_2 feq fneg1_ne_0, ← sub_eq_add_neg, sub_eq_add_neg 2 x, add_comm, this],
    exact le_of_lt (neg_lt_zero.mpr h0) },
  intros x h,
  obtain ⟨u, rfl⟩ := extra.real_poly_range1 h,
  rw sub_eq_sub_iff_sub_eq_sub,
  nth_rewrite 6 ← add_sub_cancel'_right u 1,
  rw [feq, ← neg_mul_neg (f u), ← lem2_2 feq fneg1_ne_0, ← lem2_2 feq fneg1_ne_0, ← feq],
  congr' 2; ring
end

private lemma lem2_4 [char_p R 2] : false :=
begin
  have h := lem2_3 feq fneg1_ne_0 (-1),
  rw [bit0, neg_add_cancel_comm_assoc, char_two.two_eq_zero, add_zero, lem1_1 feq, eq_comm] at h,
  exact fneg1_ne_0 h
end

private lemma lem2_5 (x : ℝ) : f (-x) = -(2 + f x) :=
begin
  have h := lem2_3 feq fneg1_ne_0 (-x),
  rw [add_comm, ← sub_eq_add_neg, lem2_2 feq fneg1_ne_0, ← sub_eq_iff_eq_add] at h,
  rw [← h, sub_eq_add_neg, add_comm, neg_add]
end

private lemma lem2_6 (char_ne_2 : ring_char R ≠ 2) (x y : ℝ) : f (x + y) = f x + f y + 1 :=
begin
  have h := feq (-x) (-y),
  rw [neg_mul_neg, ← neg_add, lem2_5 feq fneg1_ne_0, sub_neg_eq_add, lem2_5 feq fneg1_ne_0,
      lem2_5 feq fneg1_ne_0, neg_mul_neg, add_mul, mul_add, mul_add, ← feq, ← sub_eq_zero] at h,
  replace h : 2 * (f (x + y) - (f x + f y + 1)) = 0 := by rw ← h; ring,
  rwa [mul_eq_zero, or_iff_right (ring.two_ne_zero char_ne_2), sub_eq_zero] at h
end

private lemma lem2_7 (char_ne_2 : ring_char R ≠ 2) : ∃ φ : ℝ →+* R, f = φ - 1 :=
begin
  use f + 1; simp,
  exact lem1_1 feq,
  intros x y,
  have h := feq x y,
  rw [sub_eq_iff_eq_add, lem2_6 feq fneg1_ne_0 char_ne_2, lem1_1 feq, zero_add] at h,
  rw [h, lem2_6 feq fneg1_ne_0 char_ne_2, add_one_mul, mul_add_one, add_assoc, add_assoc],
  rw [lem2_1 feq fneg1_ne_0, neg_add_self],
  intros x y; rw [lem2_6 feq fneg1_ne_0 char_ne_2, add_assoc, add_add_add_comm]
end

end case_fneg1_ne_0



section case_fneg1_eq_0

variable (fneg1_eq_0 : f (-1) = 0)
include fneg1_eq_0

private lemma lem3_1 (x : ℝ) : f (-x) = f x :=
begin
  have h := lem1_3 feq x,
  rwa [fneg1_eq_0, zero_mul, sub_eq_zero, eq_comm] at h
end

private lemma lem3_2 (u v : ℝ≥0) : f (1 + v / 4) - f (1 - v / 4) = f (sqrt (u + v)) - f (sqrt u) :=
begin
  rcases extra.real_mv_poly_range1 u v with ⟨x, y, h, h0⟩,
  simp only [real.coe_sqrt],
  rw [nonneg.coe_add, h, h0, mul_div_cancel_left (x * y) four_ne_zero]; clear h h0 u v,
  have h : (x - y) ^ 2 + 4 * (x * y) = (x + y) ^ 2 := by ring,
  rw h; replace h := lem3_1 feq fneg1_eq_0,
  rw [real.sqrt_sq_eq_abs, extra.f_abs_eq_of_even h, real.sqrt_sq_eq_abs, extra.f_abs_eq_of_even h,
      sub_eq_sub_iff_sub_eq_sub, feq, ← h y, ← feq, mul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg]
end

variable (f0_eq_neg1 : f 0 = -1)
include f0_eq_neg1

private lemma lem3_3 (u v : ℝ≥0) : f (sqrt (u + v)) = f (sqrt u) + f (sqrt v) + 1 :=
  by rw [add_assoc, ← sub_eq_iff_eq_add', ← lem3_2 feq fneg1_eq_0, lem3_2 feq fneg1_eq_0 0,
         zero_add, sqrt_zero, nonneg.coe_zero, sub_eq_add_neg, f0_eq_neg1, neg_neg]

private lemma lem3_4 (u v : ℝ≥0) : f (sqrt (u * v)) + 1 = (f (sqrt u) + 1) * (f (sqrt v) + 1) :=
begin
  rcases extra.exists_eq_nnabs_sq u with ⟨x, rfl⟩,
  rcases extra.exists_eq_nnabs_sq v with ⟨y, rfl⟩,
  suffices h : ∀ u v : ℝ≥0, f (u + v) = f u + f v + f (sqrt (2 * u * v)) + 2,
    rw [sqrt_mul, sqrt_sq, sqrt_sq, add_one_mul, mul_add_one, ← add_assoc, add_left_inj, add_assoc,
        ← feq, h, ← nonneg.coe_one, ← nonneg.coe_mul, h, nonneg.coe_one, lem1_1 feq, zero_add,
        mul_one, mul_assoc, add_sub_add_right_eq_sub, add_sub_add_right_eq_sub, sub_add_cancel],
  intros u v,
  have h := lem3_3 feq fneg1_eq_0 f0_eq_neg1,
  rw [← nonneg.coe_add, ← sqrt_sq (u + v), add_sq, h, sqrt_sq, h, sqrt_sq,
      add_right_comm _ 1 (f v), add_right_comm (f u), add_assoc]; refl
end

private lemma lem3_5 : ∃ φ : ℝ≥0 →+* R, f = λ x : ℝ, φ (x.nnabs ^ 2) - 1 :=
begin
  use λ x, f (sqrt x) + 1,
  rw [sqrt_one, nonneg.coe_one, lem1_1 feq, zero_add],
  exact lem3_4 feq fneg1_eq_0 f0_eq_neg1,
  rw [sqrt_zero, nonneg.coe_zero, f0_eq_neg1, neg_add_self],
  intros x y; rw [lem3_3 feq fneg1_eq_0 f0_eq_neg1, add_add_add_comm, add_assoc],
  funext x,
  rw [ring_hom.coe_mk, add_sub_cancel, sqrt_sq, real.coe_nnabs,
      extra.f_abs_eq_of_even (lem3_1 feq fneg1_eq_0)]
end

end case_fneg1_eq_0

end results



/-- Final solution -/
theorem final_solution_general (f : ℝ → R) : fn_eq f ↔
  f = 0 ∨ (∃ φ : ℝ →+* R, f = φ - 1) ∨ (∃ φ : ℝ≥0 →+* R, f = λ x : ℝ, φ (x.nnabs ^ 2) - 1) :=
begin
  split,
  { intros feq,
    cases ne_or_eq (f 0) (-1) with h h,
    left; exact lem1_2 feq h,
    right; cases eq_or_ne (f (-1)) 0 with h0 h0,
    right; exact lem3_5 feq h0 h,
    left; cases eq_or_ne (ring_char R) 2 with h1 h1,
    rw ring_char.eq_iff at h1,
    exfalso; exactI lem2_4 feq h0,
    exact lem2_7 feq h0 h1 },
  { rintros (rfl | ⟨φ, rfl⟩ | ⟨φ, rfl⟩) x y,
    simp only [pi.zero_apply]; rw [sub_zero, mul_zero],
    simp only [pi.sub_apply, pi.one_apply, map_add],
    rw [map_one, add_sub_cancel', map_mul, add_sub_assoc, ← sub_sub, sub_one_mul, mul_sub_one],
    simp only [],
    sorry }
end

/-- Final solution, case char(R) ≠ 0 -/
theorem final_solution_char_ne_0 (p : ℕ) [fact (p ≠ 0)] [char_p R p] (f : ℝ → R) :
    fn_eq f ↔ f = 0 :=
  by rw [final_solution_general, is_empty.exists_iff, is_empty.exists_iff, or_false, or_false]

end IMO2012A5
end IMOSL
