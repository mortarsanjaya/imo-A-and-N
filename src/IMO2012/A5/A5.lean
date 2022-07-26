import
  data.real.sqrt
  algebra.char_p.basic
  extra.real_quadratic_sol
  extra.real_hom.semifield_char0_hom
  extra.real_hom.nnreal_semifield
  extra.real_hom.nnreal_odd_ext

/-! # IMO 2012 A5, Generalized Version -/

open function nnreal
open_locale nnreal classical

namespace IMOSL
namespace IMO2012A5

def fn_eq {R : Type*} [ring R] (f : ℝ → R) := ∀ x y : ℝ, f (1 + x * y) - f(x + y) = f x * f y



section results

variables {R : Type*} [comm_ring R] [is_domain R] {f : ℝ → R} (feq : fn_eq f)
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
begin
  contrapose! fneg1_ne_0 with f0_ne_neg1,
  rw [lem1_2 feq f0_ne_neg1, pi.zero_apply]
end

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
  obtain ⟨u, v, h0, h1⟩ : ∃ u v : ℝ, u + v = 1 ∧ u * v = x - 1 :=
  begin
    refine extra.exists_add_eq_mul_eq _ _ (le_trans _ (sq_nonneg 1)),
    exact mul_nonpos_of_nonneg_of_nonpos zero_le_four (sub_nonpos_of_le (le_trans h zero_le_one))
  end,
  have h2 := feq (2 - u) (2 - v),
  rwa [lem2_2 feq fneg1_ne_0, lem2_2 feq fneg1_ne_0, neg_mul_neg, sub_add_sub_comm,
       mul_sub, sub_mul, sub_mul, sub_sub, ← add_sub_assoc (u * 2), mul_comm u 2,
       ← mul_add, ← feq, h0, h1, ← sub_add, add_comm, add_comm 1 (x - 1), add_assoc,
       sub_add_cancel, ← mul_sub, bit0, add_sub_cancel, mul_one, add_sub_assoc,
       add_sub_cancel, ← bit0, ← bit1, add_comm 2 x, sub_eq_sub_iff_sub_eq_sub] at h2
end

private lemma lem2_4 (x : ℝ) : f (-x) = -(2 + f x) :=
begin
  have h := lem2_3 feq fneg1_ne_0 (-x),
  rw [add_comm, ← sub_eq_add_neg, lem2_2 feq fneg1_ne_0, ← sub_eq_iff_eq_add] at h,
  rw [← h, sub_eq_add_neg, add_comm, neg_add]
end

private lemma lem2_5 (x y : ℝ) : f (x + y) = f x + f y + 1 :=
begin
  have h := feq (-x) (-y),
  rw [neg_mul_neg, ← neg_add, lem2_4 feq fneg1_ne_0, sub_neg_eq_add, lem2_4 feq fneg1_ne_0,
      lem2_4 feq fneg1_ne_0, neg_mul_neg, add_mul, mul_add, mul_add, ← feq, ← sub_eq_zero] at h,
  replace h : 2 * (f (x + y) - (f x + f y + 1)) = 0 := by rw ← h; ring,
  rwa [mul_eq_zero, sub_eq_zero, or_comm] at h,
  cases h with h h,
  exact h,
  have h0 := lem2_3 feq fneg1_ne_0 (-1),
  rw [bit0, neg_add_cancel_comm_assoc, h, add_zero, lem1_1 feq, eq_comm] at h0,
  exfalso; exact fneg1_ne_0 h0
end

private lemma lem2_6 : ∃ φ : ℝ →+* R, f = φ - 1 :=
begin
  use f + 1; simp,
  exact lem1_1 feq,
  intros x y,
  have h := feq x y,
  rw [sub_eq_iff_eq_add, lem2_5 feq fneg1_ne_0, lem1_1 feq, zero_add] at h,
  rw [h, lem2_5 feq fneg1_ne_0, add_one_mul, mul_add_one, add_assoc, add_assoc],
  rw [lem2_1 feq fneg1_ne_0, neg_add_self],
  intros x y; rw [lem2_5 feq fneg1_ne_0, add_assoc, add_add_add_comm]
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
  obtain ⟨x, y, h, h0⟩ : ∃ x y : ℝ, x + y = sqrt (u + v) ∧ x * y = v / 4 :=
  begin
    apply extra.exists_add_eq_mul_eq,
    rw [real.coe_sqrt, nonneg.coe_add, real.sq_sqrt, mul_div_cancel'],
    exacts [le_add_of_nonneg_left (coe_nonneg u), four_ne_zero,
            add_nonneg (coe_nonneg u) (coe_nonneg v)]
  end,
  rw [← h, ← h0, sub_eq_sub_iff_sub_eq_sub, feq, ← lem3_1 feq fneg1_eq_0 y,
      ← feq, mul_neg, ← sub_eq_add_neg, sub_right_inj, ← sub_eq_add_neg],
  suffices : (u : ℝ) = (x - y) ^ 2,
  { rw [real.coe_sqrt, this, real.sqrt_sq_eq_abs],
    cases le_total 0 (x - y) with h1 h1,
    rw abs_eq_self.mpr h1,
    rw [abs_eq_neg_self.mpr h1, lem3_1 feq fneg1_eq_0] },
  replace h := congr_arg (λ x, x ^ 2) h; simp only [] at h,
  rw [← nonneg.coe_pow, sq_sqrt, nonneg.coe_add, ← sub_eq_iff_eq_add] at h,
  rw [← h, sub_eq_iff_eq_add', ← sub_eq_iff_eq_add, add_sq, sub_sq, add_sub_add_right_eq_sub,
      add_sub_sub_cancel, mul_assoc, ← add_mul, h0, ← bit0, mul_div_cancel'],
  exact four_ne_zero
end

variable (f0_eq_neg1 : f 0 = -1)
include f0_eq_neg1

private lemma lem3_3 (u v : ℝ≥0) : f (sqrt (u + v)) = f (sqrt u) + f (sqrt v) + 1 :=
  by rw [add_assoc, ← sub_eq_iff_eq_add', ← lem3_2 feq fneg1_eq_0, lem3_2 feq fneg1_eq_0 0,
         zero_add, sqrt_zero, nonneg.coe_zero, sub_eq_add_neg, f0_eq_neg1, neg_neg]

private lemma lem3_4 (u v : ℝ≥0) : f (u * v) + 1 = (f u + 1) * (f v + 1) :=
begin
  revert u v; suffices : ∀ u v : ℝ≥0, f (u + v) = f u + f v + f (sqrt (2 * u * v)) + 2,
  { intros u v,
    have h := feq u v,
    rw [← nonneg.coe_one, ← nonneg.coe_mul, this, nonneg.coe_one, ← lem3_1 feq fneg1_eq_0,
        fneg1_eq_0, zero_add, mul_one, this, add_sub_add_right_eq_sub, mul_assoc,
        add_sub_add_right_eq_sub, nonneg.coe_mul, sub_eq_iff_eq_add, ← add_assoc] at h,
    rw [h, add_one_mul, mul_add_one, ← add_assoc] },
  intros u v,
  have h := lem3_3 feq fneg1_eq_0 f0_eq_neg1,
  rw [← nonneg.coe_add, ← sqrt_sq (u + v), add_sq, h, sqrt_sq, h, sqrt_sq,
      add_right_comm _ 1 (f v), add_right_comm (f u), add_assoc, ← bit0]
end

private lemma lem3_5 : ∃ φ : ℝ≥0 →+* R, f = λ x : ℝ, φ (x.nnabs ^ 2) - 1 :=
begin
  use λ x, f (sqrt x) + 1,
  rw [sqrt_one, nonneg.coe_one, lem1_1 feq, zero_add],
  intros x y; rw [sqrt_mul, nonneg.coe_mul, lem3_4 feq fneg1_eq_0 f0_eq_neg1],
  rw [sqrt_zero, nonneg.coe_zero, f0_eq_neg1, neg_add_self],
  intros x y; rw [lem3_3 feq fneg1_eq_0 f0_eq_neg1, add_add_add_comm, add_assoc],
  funext x,
  rw [ring_hom.coe_mk, add_sub_cancel, sqrt_sq, real.coe_nnabs],
  cases le_total 0 x with h h,
  rw abs_eq_self.mpr h,
  rw [abs_eq_neg_self.mpr h, lem3_1 feq fneg1_eq_0]
end

end case_fneg1_eq_0

end results



/-- Final solution -/
theorem final_solution_general {R : Type*} [comm_ring R] [is_domain R] (f : ℝ → R) : fn_eq f ↔
  f = 0 ∨ (∃ φ : ℝ →+* R, f = φ - 1) ∨ (∃ φ : ℝ≥0 →+* R, f = λ x : ℝ, φ (x.nnabs ^ 2) - 1) :=
begin
  split,
  { intros feq,
    cases ne_or_eq (f 0) (-1) with h h,
    left; exact lem1_2 feq h,
    right; cases eq_or_ne (f (-1)) 0 with h0 h0,
    right; exact lem3_5 feq h0 h,
    left; exact lem2_6 feq h0 },
  { rintros (rfl | ⟨φ, rfl⟩ | ⟨φ, h⟩) x y,
    simp only [pi.zero_apply]; rw [sub_zero, mul_zero],
    simp only [pi.sub_apply, pi.one_apply, map_add],
    rw [map_one, add_sub_cancel', map_mul, add_sub_assoc, ← sub_sub, sub_one_mul, mul_sub_one],
    replace h : f = λ x, (φ : ℝ →+* R) (x ^ 2) - 1 :=
    begin
      subst h; funext x,
      rw [← extra.nnreal_ring_hom.coe_fn_apply, nnreal.coe_pow, real.coe_nnabs, pow_bit0_abs]
    end,
    subst h; simp only [],
    rw [add_sq, add_sq, one_pow, mul_one, sub_sub_sub_cancel_right, add_right_comm, mul_assoc,
        add_right_comm (x ^ 2), map_add, map_add, map_add, add_sub_add_right_eq_sub,
        map_one, map_add, mul_pow, map_mul, sub_one_mul, mul_sub_one, sub_sub, ← add_sub_assoc,
        ← sub_add, add_comm, add_sub_right_comm] }
end

/-- Final solution, case char(R) ≠ 0 -/
theorem final_solution_char_ne_0 {R : Type*} [comm_ring R] [is_domain R]
    (p : ℕ) [fact (p ≠ 0)] [char_p R p] (f : ℝ → R) : fn_eq f ↔ f = 0 :=
  by rw [final_solution_general, is_empty.exists_iff, is_empty.exists_iff, or_false, or_false]

/-- Final solution, case R = ℝ -/
theorem final_solution_real (f : ℝ → ℝ) : fn_eq f ↔ f = 0 ∨ (f = id - 1) ∨ (f = λ x, x ^ 2 - 1) :=
begin
  rw [final_solution_general, unique.exists_iff, unique.exists_iff],
  unfold default,
  rw ring_hom.coe_one,
  refine or_congr_right' (or_congr_right' _),
  conv_lhs { to_rhs, funext, rw [coe_to_real_hom, coe_pow, real.coe_nnabs, sq_abs] }
end

end IMO2012A5
end IMOSL
