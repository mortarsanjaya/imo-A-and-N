import
  data.real.basic
  algebra.algebra.basic
  data.real.golden_ratio
  analysis.special_functions.pow

/-! # IMO 2021 A8, Generalized Version -/

open function real
open_locale classical

namespace IMOSL
namespace IMO2021A8

variables {R : Type*} [comm_ring R] [is_domain R]

def fn_eq (f : ℝ → R) := ∀ a b c : ℝ, (f(a) - f(b)) * (f(b) - f(c)) * (f(c) - f(a))
  = f(a * b ^ 2 + b * c ^ 2 + c * a ^ 2) - f(b * a ^ 2 + c * b ^ 2 + a * c ^ 2)



section results

variables {f : ℝ → R} (feq : fn_eq f)
include feq

private lemma lem1_1 (C : R) : fn_eq (f + const ℝ C) :=
  by simp only [fn_eq, const_apply, add_sub_add_right_eq_sub, pi.add_apply]; exact feq

private lemma lem1_2 : fn_eq (-f) :=
begin
  intros a b c,
  simp only [pi.neg_apply],
  repeat { rw ← neg_sub' },
  rw [neg_mul_neg, mul_neg, feq]
end



private lemma lem2_1 {c : ℝ} (c_ne_0 : c ≠ 0) (h : f c = f 0) (x : ℝ) : f (-x) = f x :=
begin
  revert x; suffices : ∀ x : ℝ, f (c * x ^ 2) = f (x * c ^ 2),
  { intros x,
    have h0 := this (-(x / (c ^ 2))),
    rwa [neg_sq, this, neg_mul, div_mul_cancel _ (pow_ne_zero 2 c_ne_0), eq_comm] at h0 },
  intros x,
  replace feq := feq x c 0,
  rwa [h, sub_self, mul_zero, zero_mul, zero_pow zero_lt_two, mul_zero, add_zero, zero_mul,
       add_zero, mul_zero, add_zero, zero_mul, add_zero, eq_comm, sub_eq_zero, eq_comm] at feq
end

private lemma lem2_2 (h : ∀ x : ℝ, f (-x) = f x) : ∃ C : R, f = const ℝ C :=
begin
  use [f 0]; ext x,
  suffices : ∃ y : ℝ, x = 2 * golden_ratio * y ^ 3,
  { cases this with y h0,
    replace feq := feq y (-y) (golden_ratio * y),
    rw [h, sub_self, zero_mul, zero_mul, eq_comm, sub_eq_zero, neg_sq, eq_comm] at feq,
    convert feq; clear feq; ring_nf,
    rw [h0, add_one_mul, ← sq, gold_sq, add_right_comm, add_sub_cancel, ← two_mul],
    rw [add_one_mul (-golden_ratio), neg_mul, add_assoc, ← sq, gold_sq, neg_add_self, zero_mul] },
  revert x; suffices : ∀ x : ℝ, 0 ≤ x → ∃ y : ℝ, x = y ^ 3,
  { intros x,
    have h0 := mul_ne_zero two_ne_zero gold_ne_zero,
    cases le_total 0 (x / (2 * golden_ratio)) with h1 h1,
    obtain ⟨y, h2⟩ := this _ h1,
    use y; rw [← h2, mul_div_cancel' x h0],
    rw ← neg_nonneg at h1; obtain ⟨y, h2⟩ := this _ h1,
    use (-y); rw [neg_pow_bit1, ← h2, neg_neg, mul_div_cancel' x h0] },
  intros x h; use x ^ (↑3 : ℝ)⁻¹,
  rw rpow_nat_inv_pow_nat h zero_lt_three
end

private lemma lem2_3 {a b : ℝ} (h : f a = f b) (h0 : a ≠ b) : ∃ c : ℝ, c ≠ 0 ∧ f c = f 0 :=
begin
  sorry
end

private theorem thm2 (h : ¬injective f) : ∃ C : R, f = const ℝ C :=
begin
  simp only [injective, not_forall] at h,
  rcases h with ⟨a, b, h, h0⟩,
  rcases lem2_3 feq h h0 with ⟨c, h1, h2⟩,
  exact lem2_2 feq (lem2_1 feq h1 h2)
end



section f_inj_f0_eq_0

variables (f_inj : injective f) (f0_eq_0 : f 0 = 0)
include f_inj f0_eq_0

private lemma lem3_1 (a b : ℝ) : (f a - f b) * f a * f b = f (b * a ^ 2) - f (a * b ^ 2) :=
begin
  replace feq := feq b a 0,
  rwa [f0_eq_0, sub_zero, zero_sub, mul_neg, ← neg_mul, ← neg_mul, neg_sub, zero_pow zero_lt_two,
       mul_zero, add_zero, zero_mul, add_zero, mul_zero, add_zero, zero_mul, add_zero] at feq
end

private lemma lem3_2 {a : ℝ} (h : a ≠ 0) : (f 1 - (f a + f (-a))) * f 1 = 1 :=
begin
  have h0 := congr_arg2 (λ x y, x - y)
    (lem3_1 feq f_inj f0_eq_0 1 a)
    (lem3_1 feq f_inj f0_eq_0 1 (-a)),
  ring_nf at h0,
  rwa [add_comm (- _^2), ← sub_eq_add_neg, ← neg_sub (_ ^ 2), ← sub_eq_add_neg, sq_sub_sq,
       mul_comm (f a - _), ← sub_mul, mul_right_comm, mul_left_eq_self₀, or_iff_left] at h0,
  clear h0; contrapose! h,
  rw sub_eq_zero at h,
  replace h := f_inj h,
  rwa eq_neg_self_iff at h
end

private lemma lem3_3 {a : ℝ} (h : a ≠ 0) (h0 : a ^ 2 ≠ 1) : f a * f a⁻¹ = 1 :=
begin
  replace feq := lem3_1 feq f_inj f0_eq_0 a a⁻¹,
  rwa [sq, ← mul_assoc, inv_mul_cancel h, one_mul, sq, ← mul_assoc, mul_inv_cancel h,
       one_mul, mul_assoc, mul_right_eq_self₀, sub_eq_zero, or_iff_left] at feq,
  contrapose! h0,
  replace h0 := f_inj h0,
  rwa [← mul_one a⁻¹, eq_inv_mul_iff_mul_eq₀ h, ← sq] at h0
end

private lemma lem3_4 {a : ℝ} (h : a ≠ 0) (h0 : a ^ 2 ≠ 1) : f (-a) = -f a :=
begin
  obtain ⟨c, h1⟩ : ∃ c : R, ∀ b : ℝ, b ≠ 0 → f (-b) = c - f b :=
  begin
    use f 1 + f (-1); intros b h1,
    rw eq_sub_iff_add_eq,
    replace h1 := lem3_2 feq f_inj f0_eq_0 h1,
    have h2 := lem3_2 feq f_inj f0_eq_0 one_ne_zero,
    rwa [sub_add_cancel', ← h1, mul_eq_mul_right_iff, eq_sub_iff_add_eq',
         add_neg_eq_iff_eq_add, add_comm, or_iff_left] at h2,
    clear h2; intros h2,
    rw [h2, mul_zero] at h1,
    exact zero_ne_one h1
  end,
  rw [h1 a h, sub_eq_neg_self],
  have h2 : f (-a) * f (-a) ⁻¹ = 1 :=
    lem3_3 feq f_inj f0_eq_0 (neg_ne_zero.mpr h) (by rwa neg_sq),
  rwa [← neg_inv, h1 a h, h1 _ (inv_ne_zero h), sub_mul, mul_sub, mul_sub, ← sub_add, sub_sub,
       lem3_3 feq f_inj f0_eq_0 h h0, add_left_eq_self, mul_comm (f a), ← mul_add, ← mul_sub,
       mul_eq_zero, sub_eq_zero, or_iff_left] at h2,
  clear h2; intros h2,
  rw [← sub_eq_iff_eq_add, ← h1 a h] at h2,
  replace h2 := f_inj h2,
  rw [← mul_one a⁻¹, eq_inv_mul_iff_mul_eq₀ h, mul_neg, ← sq] at h2,
  replace h1 := sq_nonneg a,
  rw [← neg_le_neg_iff, h2, neg_zero, ← not_lt] at h1,
  exact h1 zero_lt_one
end

private theorem thm3_1 : (f 1) ^ 2 = 1 :=
begin
  have h := lem3_2 feq f_inj f0_eq_0 two_ne_zero,
  rwa [lem3_4 feq f_inj f0_eq_0 two_ne_zero (by norm_num), add_neg_self, sub_zero, ← sq] at h
end

private lemma lem3_5 (a : ℝ) : f (-a) = -f a :=
begin
  rcases eq_or_ne a 0 with rfl | h,
  rw [neg_zero, f0_eq_0, neg_zero],
  replace h := lem3_2 feq f_inj f0_eq_0 h,
  have h0 := thm3_1 feq f_inj f0_eq_0,
  rw [sub_mul, ← sq, h0, sub_eq_self, mul_eq_zero, or_iff_left] at h,
  rwa [add_comm, add_eq_zero_iff_eq_neg] at h,
  intros h1,
  rw [h1, zero_pow zero_lt_two] at h0,
  exact zero_ne_one h0
end

private theorem thm3_2 (f1_eq_1 : f 1 = 1) (a b : ℝ) : f (a * b) = f a * f b :=
begin
  revert a b; suffices : ∀ a b : ℝ, 0 ≤ a → f (a * b) = f a * f b,
  { intros a b,
    cases le_total 0 a with h h,
    exact this a b h,
    rw [← neg_le_neg_iff, neg_zero] at h,
    replace this := this _ b h,
    replace h := lem3_5 feq f_inj f0_eq_0,
    rwa [neg_mul, h, h, neg_mul, neg_inj] at this },
  suffices : ∀ a b : ℝ, f (a ^ 2 * b) = f a ^ 2 * f b,
  { intros a b h,
    replace this := this (sqrt a),
    conv at this { find (_ = _) { rw [sq_sqrt h] } },
    replace h := this 1,
    rw [mul_one, f1_eq_1, mul_one] at h,
    rw [this, ← h] },
  intros a b,
  have h := congr_arg2 (λ x y, x - y)
    (lem3_1 feq f_inj f0_eq_0 a b)
    (lem3_1 feq f_inj f0_eq_0 a (-b)),
  simp only [] at h,
  rw [neg_sq, lem3_5 feq f_inj f0_eq_0, neg_mul, lem3_5 feq f_inj f0_eq_0] at h,
  ring_nf at h,
  rwa [mul_assoc, mul_eq_mul_left_iff, or_iff_left, mul_comm, eq_comm] at h,
  clear h; intros h,
  replace h : f 1 = f (-1) :=
    by rw [lem3_5 feq f_inj f0_eq_0, f1_eq_1, eq_neg_iff_add_eq_zero, ← bit0, h],
  replace h := f_inj h,
  rw [eq_neg_iff_add_eq_zero, ← bit0] at h,
  exact two_ne_zero h
end

end f_inj_f0_eq_0

end results





end IMO2021A8
end IMOSL
