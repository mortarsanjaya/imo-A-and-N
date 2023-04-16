import
  data.real.sqrt
  extra.real_hom.semifield_char0_hom
  extra.real_hom.nnreal_odd_ext
  extra.real_prop.real_quadratic_sol

/-! # IMO 2012 A5 -/

namespace IMOSL
namespace IMO2012A5

open function nnreal
open_locale nnreal

def good {R S : Type*} [ring R] [ring S] (f : R → S) :=
  ∀ x y : R, f (1 + x * y) - f(x + y) = f x * f y



section extra_lemmas

private lemma one_add_mul_sub_add {R : Type*} [ring R] (x y : R) :
  (1 + x * y) - (x + y) = (x - 1) * (y - 1) :=
  by rw [add_comm, ← sub_add_sub_comm, ← mul_sub_one,
    ← neg_sub y, ← sub_eq_add_neg, ← sub_one_mul]

private lemma one_add_mul_add_add {R : Type*} [ring R] (x y : R) :
  (1 + x * y) + (x + y) = (x + 1) * (y + 1) :=
  by rw [add_add_add_comm, ← add_one_mul, add_comm 1 x, ← mul_one_add, add_comm 1 y]

end extra_lemmas





section basic_results

section answer

variables {R S : Type*} [ring R]

private lemma good_zero [ring S] : good (λ (_ : R), (0 : S)) :=
  λ x y, by rw [sub_zero, mul_zero]

private lemma good_hom_sub_one [ring S] (φ : R →+* S) :
  good (λ (x : R), φ x - 1) :=
  λ x y, by rw [sub_sub_sub_cancel_right, φ.map_add, φ.map_one, φ.map_add, φ.map_mul];
    exact one_add_mul_sub_add (φ x) (φ y)

private lemma good_hom_sq_sub_one [comm_ring S] (φ : R →+* S) :
  good (λ (x : R), φ x ^ 2 - 1) :=
  λ x y, by rw [sub_sub_sub_cancel_right, φ.map_add, φ.map_one, φ.map_add, φ.map_mul, sq_sub_sq,
    one_add_mul_sub_add, one_add_mul_add_add, mul_mul_mul_comm, ← sq_sub_sq, ← sq_sub_sq, one_pow]

end answer


private lemma good_subst_neg_one {R S : Type*} [ring R] [ring S] {f : R → S} (h : good f) (x : R) :
  f x - f (-x) = f (-1) * f (1 - x) :=
  by rw [← h, neg_one_mul, neg_sub, add_sub_cancel'_right, ← add_sub_assoc, neg_add_self, zero_sub]


section domain

variables {R S : Type*} [ring R] [comm_ring S] [is_domain S] {f : R → S} (h : good f)
include h

private lemma good_map_one : f 1 = 0 :=
  by replace h := h 1 1; rwa [mul_one, sub_self, zero_eq_mul_self] at h

private lemma good_eq_zero_of_map_zero_ne_neg_one (h0 : f 0 ≠ -1) : f = 0 :=
  funext (λ x, by have h1 := h x 0; rwa [mul_zero, add_zero, good_map_one h, zero_sub,
    add_zero, ← mul_neg_one, mul_eq_mul_left_iff, or_iff_right h0.symm] at h1)

end domain

end basic_results














section results

variables {R : Type*} [comm_ring R] [is_domain R] {f : ℝ → R} (feq : good f)
include feq


section case_fneg1_ne_0

variable (fneg1_ne_0 : f (-1) ≠ 0)
include fneg1_ne_0

private lemma lem2_1 : f 0 = -1 :=
begin
  contrapose! fneg1_ne_0 with f0_ne_neg1,
  rw [good_eq_zero_of_map_zero_ne_neg_one feq f0_ne_neg1, pi.zero_apply]
end

private lemma lem2_2 (x : ℝ) : f (2 - x) = -f x :=
begin
  have h := good_subst_neg_one feq (-(1 - x)),
  rwa [neg_neg, ← neg_sub, good_subst_neg_one feq (1 - x), ← mul_neg, mul_eq_mul_left_iff,
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
    cases le_total x 0 with h0 h0,
    rw [← sub_eq_iff_eq_add', this x h0],
    rw [← this (-x) (by rwa neg_nonpos), add_comm (-x), ← sub_eq_add_neg,
        lem2_2 feq fneg1_ne_0, ← add_sub_assoc, add_neg_self, zero_sub,
        ← lem2_2 feq fneg1_ne_0, sub_neg_eq_add, add_comm] },
  intros x h,
  obtain ⟨u, v, h0, h1⟩ : ∃ u v : ℝ, u + v = 1 ∧ u * v = x - 1 :=
  begin
    refine extra.exists_add_eq_mul_eq (le_trans _ (sq_nonneg 1)),
    exact mul_nonpos_of_nonneg_of_nonpos zero_le_four (sub_nonpos_of_le (le_trans h zero_le_one))
  end,
  have h2 := feq (2 - u) (2 - v),
  rw [lem2_2 feq fneg1_ne_0, lem2_2 feq fneg1_ne_0, neg_mul_neg, ← feq, h1,
      sub_add_sub_comm, h0, sub_eq_sub_iff_sub_eq_sub, add_sub_cancel'_right] at h2,
  convert h2 using 3,
  work_on_goal 2 { rw [eq_sub_iff_add_eq, bit1, add_assoc, ← bit0] },
  rw [add_comm (1 : ℝ), ← sub_eq_sub_iff_add_eq_add, ← h1, sub_mul, mul_sub,
      mul_sub, ← sub_add, sub_sub, mul_comm u 2, ← mul_add, add_comm v u, h0,
      mul_one, two_mul, add_sub_cancel, add_sub_cancel']
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
  rw [bit0, neg_add_cancel_comm_assoc, h, add_zero, good_map_one feq, eq_comm] at h0,
  exfalso; exact fneg1_ne_0 h0
end

private lemma lem2_6 : ∃ φ : ℝ →+* R, f = φ - 1 :=
begin
  use f + 1; simp,
  exact good_map_one feq,
  intros x y,
  have h := feq x y,
  rw [sub_eq_iff_eq_add, lem2_5 feq fneg1_ne_0, good_map_one feq, zero_add] at h,
  rw [h, lem2_5 feq fneg1_ne_0, add_one_mul, mul_add_one, add_assoc, add_assoc],
  rw [lem2_1 feq fneg1_ne_0, neg_add_self],
  intros x y; rw [lem2_5 feq fneg1_ne_0, add_assoc, add_add_add_comm]
end

end case_fneg1_ne_0



section case_fneg1_eq_0

variable (fneg1_eq_0 : f (-1) = 0)
include fneg1_eq_0

private lemma lem3_1 (x : ℝ) : f (-x) = f x :=
  by rw [eq_comm, ← sub_eq_zero, good_subst_neg_one feq x, fneg1_eq_0, zero_mul]

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
  rw [sqrt_one, nonneg.coe_one, good_map_one feq, zero_add],
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
theorem final_solution_general {R : Type*} [comm_ring R] [is_domain R] (f : ℝ → R) : good f ↔
  f = 0 ∨ (∃ φ : ℝ →+* R, f = φ - 1) ∨ (∃ φ : ℝ≥0 →+* R, f = λ x : ℝ, φ (x.nnabs ^ 2) - 1) :=
begin
  split,
  { intros feq,
    cases ne_or_eq (f 0) (-1) with h h,
    left; exact good_eq_zero_of_map_zero_ne_neg_one feq h,
    right; cases eq_or_ne (f (-1)) 0 with h0 h0,
    right; exact lem3_5 feq h0 h,
    left; exact lem2_6 feq h0 },
  { rintros (rfl | ⟨φ, rfl⟩ | ⟨φ, h⟩),
    exact good_zero,
    exact good_hom_sub_one φ,
    intros x y,
    conv at h { congr, skip, funext,
      rw [← extra.nnreal_ring_hom.coe_fn_apply, nnreal.coe_pow, real.coe_nnabs, pow_bit0_abs] },
    subst h; simp only [],
    rw [add_sq, add_sq, one_pow, mul_one, sub_sub_sub_cancel_right, add_right_comm, mul_assoc,
        add_right_comm (x ^ 2), map_add, map_add, map_add, add_sub_add_right_eq_sub,
        map_one, map_add, mul_pow, map_mul, sub_one_mul, mul_sub_one, sub_sub, ← add_sub_assoc,
        ← sub_add, add_comm, add_sub_right_comm] }
end

/-- Final solution, case char(R) ≠ 0 -/
theorem final_solution_char_ne_0 {R : Type*} [comm_ring R] [is_domain R]
    (p : ℕ) [fact (p ≠ 0)] [char_p R p] (f : ℝ → R) : good f ↔ f = 0 :=
  by rw [final_solution_general, is_empty.exists_iff, is_empty.exists_iff, or_false, or_false]

/-- Final solution, case R = ℝ -/
theorem final_solution_real (f : ℝ → ℝ) : good f ↔ f = 0 ∨ (f = id - 1) ∨ (f = λ x, x ^ 2 - 1) :=
begin
  rw [final_solution_general, unique.exists_iff, unique.exists_iff],
  unfold default; refine or_congr_right' (or_congr_right' _),
  conv_lhs { congr, skip, funext,
    rw [nnreal.coe_to_real_hom, nnreal.coe_pow, real.coe_nnabs, pow_bit0_abs] }
end

end IMO2012A5
end IMOSL
