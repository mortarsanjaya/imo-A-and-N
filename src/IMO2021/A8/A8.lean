import
  data.real.golden_ratio
  algebra.order.complete_field
  extra.real_hom.semifield_char0_hom
  extra.real_prop.real_nat_root
  extra.real_prop.real_quadratic_sol
  

/-! # IMO 2021 A8, Generalized Version -/

namespace IMOSL
namespace IMO2021A8

open function real IMOSL.extra.real

def fn_eq {R : Type*} [ring R] (f : ℝ → R) := ∀ a b c : ℝ, (f a - f b) * (f b - f c) * (f c - f a)
  = f(a * b ^ 2 + b * c ^ 2 + c * a ^ 2) - f(b * a ^ 2 + c * b ^ 2 + a * c ^ 2)



section extra

variables {R : Type*} [add_comm_monoid R] {S : Type*} [comm_ring S] [is_domain S]

private lemma add_cube_cube_add_eq (S3ne0 : (3 : S) ≠ 0) {t u v : S}
    (h : (t + u) ^ 3 + v ^ 3 = (u + v) ^ 3 + t ^ 3) :
  t + u + v = 0 ∨ u = 0 ∨ v = t :=
begin
  rw ← sub_eq_zero at h,
  replace h : -((t + u + v) * (u * (v - t)) * 3) = 0 := by rw ← h; ring,
  rwa [neg_eq_zero, mul_eq_zero, or_iff_left S3ne0, mul_eq_zero, mul_eq_zero, sub_eq_zero] at h
end

private lemma add_cube_cube_add_zero_triple {t u v : S} (h : (t + u) ^ 3 + v ^ 3 = 0)
    (h0 : (u + v) ^ 3 + t ^ 3 = 0) (h1 : (v + t) ^ 3 + u ^ 3 = 0) : t + u + v = 0 :=
begin
  cases eq_or_ne ((3 : ℕ) : S) 0 with S3eq0 S3ne0,
  { replace S3eq0 := char_p.ring_char_of_prime_eq_zero nat.prime_three S3eq0,
    rw ring_char.eq_iff at S3eq0,
    unfreezingI { rw ← add_pow_char at h },
    exact pow_eq_zero h },
  { rw [nat.cast_bit1, nat.cast_one] at S3ne0,
    replace h1 : v + t + u = 0 ∨ t = 0 ∨ u = v :=
      by rw ← h at h1; exact add_cube_cube_add_eq S3ne0 h1,
    replace h : t + u + v = 0 ∨ u = 0 ∨ v = t :=
      by rw ← h0 at h; exact add_cube_cube_add_eq S3ne0 h,
    cases h with h h,
    exact h,
    rw [add_assoc, add_comm] at h1,
    cases h1 with h1 h1,
    exact h1,
    rcases h with rfl | rfl,
    { rw @eq_comm _ 0 v at h1,
      rcases h1 with rfl | rfl,
      rw [zero_pow zero_lt_three, add_zero, zero_add] at h0,
      rw [zero_add, zero_add]; exact pow_eq_zero h0,
      rw [add_zero, zero_pow zero_lt_three, zero_add] at h0,
      rw [add_zero, add_zero]; exact pow_eq_zero h0 },
    { rcases h1 with rfl | rfl,
      rw [add_zero, zero_pow zero_lt_three, add_zero] at h0,
      rw [zero_add, add_zero]; exact pow_eq_zero h0,
      rw [← two_mul, mul_pow, ← add_one_mul, mul_eq_zero, or_iff_right] at h0,
      rw [pow_eq_zero h0, add_zero, add_zero],
      clear h0; intros h0,
      replace h0 : (3 : S) ^ 2 = 0 := by rw ← h0; norm_num,
      exact S3ne0 (pow_eq_zero h0) } },
end

private lemma g_sum_zero_of_g_cube_sum_zero {g : R → S}
  (h : ∀ x y z : R, x + y + z = 0 → (g x + g y) ^ 3 + g z ^ 3 = 0) :
  ∀ x y z : R, x + y + z = 0 → g x + g y + g z = 0 :=
begin
  intros x y z hs,
  have hxyz := h x y z hs,
  rw [add_assoc, add_comm] at hs,
  have hyzx := h y z x hs,
  rw [add_assoc, add_comm] at hs,
  have hzxy := h z x y hs,
  exact add_cube_cube_add_zero_triple hxyz hyzx hzxy
end

private lemma g_sum_cube_eq_sum_g_cube {R : Type*} [add_comm_group R] {g : R → S}
  (h : ∀ x y : R, (g (x + y)) ^ 3 = (g x + g y) ^ 3) (h0 : ∀ x : R, g (-x) = -g x) :
  ∀ x y : R, g (x + y) = g x + g y :=
begin
  suffices : ∀ x y z : R, x + y + z = 0 → g x + g y + g z = 0,
  { intros x y,
    replace this := this x y (-(x + y)) (add_neg_self _),
    rwa [h0, add_neg_eq_zero, eq_comm] at this },
  apply g_sum_zero_of_g_cube_sum_zero; intros x y z h1,
  rw add_eq_zero_iff_neg_eq at h1,
  rw [← h1, h0, ← h, neg_pow_bit1, add_neg_self]
end

end extra




section results

private lemma lem1_1 {R : Type*} [ring R] {f : ℝ → R} (C : R) : fn_eq (f + const ℝ C) ↔ fn_eq f :=
  by simp only [fn_eq, const_apply, add_sub_add_right_eq_sub, pi.add_apply]

private lemma lem1_2 {R : Type*} [ring R] {f : ℝ → R} : fn_eq (-f) ↔ fn_eq f :=
begin
  simp only [fn_eq, pi.neg_apply],
  conv_lhs { find (_ = _) { rw [← neg_sub', ← neg_sub', neg_mul_neg,
    ← neg_sub', ← neg_sub', mul_neg, neg_inj] } }
end

private lemma lem1_3 {t : ℝ} (h : t < 2⁻¹) : ∃ x : ℝ, t ^ 2 + t * x ^ 2 + x = 0 :=
begin
  rcases eq_or_ne t 0 with rfl | h0,
  use 0; rw [zero_mul, sq, zero_mul, add_zero, add_zero],
  obtain ⟨x, h1⟩ : ∃ x : ℝ, x ^ 2 + t⁻¹ * x + t = 0 :=
  begin
    apply extra.exists_root_quadr,
    cases le_or_lt t 0 with h1 h1,
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos zero_le_four h1) (sq_nonneg _),
    rw lt_inv h1 two_pos at h,
    rw [← le_div_iff h1, div_eq_mul_inv, ← pow_succ'],
    refine le_trans (by norm_num) (pow_le_pow_of_le_left zero_le_two (le_of_lt h) 3)
  end,
  replace h1 := congr_arg (has_mul.mul t) h1,
  rw [mul_zero, mul_add, ← sq, mul_add, ← mul_assoc, mul_inv_cancel h0, one_mul] at h1,
  use x; rwa [add_assoc, add_comm]
end



section f_not_inj

variables {R : Type*} [ring R]

/-- Useful definition for the case where f is not injective -/
private def good (f : ℝ → R) (t : ℝ) := ∃ c : ℝ, c ≠ 0 ∧ f (c * t) = f c

variables {f : ℝ → R} (feq : fn_eq f)
include feq

private lemma lem2_1 {t x : ℝ} (h : f (x * t) = f x) (d : ℝ) :
  f (x ^ 3 * (t + d ^ 2 + d * t ^ 2)) = f (x ^ 3 * (t ^ 2 + d + t * d ^ 2)) :=
begin
  replace feq := feq (x * t) x (x * d),
  rwa [h, sub_self, zero_mul, zero_mul, eq_comm, sub_eq_zero] at feq,
  convert feq; ring
end

private lemma lem2_2 (h : ∃ c : ℝ, f c = f 0 ∧ c ≠ 0) (x : ℝ) : f (-x) = f x :=
begin
  rcases h with ⟨c, h, h0⟩,
  replace h := lem2_1 feq (by rw [mul_zero, h] : f (c * 0) = f c),
  ring_nf at h,
  have h1 := h (-(x / c ^ 3)),
  rwa [neg_sq, h, neg_mul, div_mul_cancel x (pow_ne_zero 3 h0), eq_comm] at h1
end

private lemma lem2_3 (h : ∀ x : ℝ, f (-x) = f x) : f = const ℝ (f 0) :=
begin
  ext x; set y := nat_root 3 (x / (2 * golden_ratio)) with hy,
  replace h := h y,
  rw ← mul_neg_one at h,
  replace h := lem2_1 feq h golden_ratio,
  rw [neg_one_sq, gold_sq] at h; ring_nf at h,
  rwa [pow_nat_root_self_bit1, mul_div_cancel' x (mul_ne_zero two_ne_zero gold_ne_zero)] at h
end

private lemma lem2_4 {t : ℝ} (h : t ≠ 0) (h0 : good f t) : good f (t ^ 4) :=
begin
  rcases h0 with ⟨c, h1, h2⟩,
  use c ^ 3 * t; split,
  exact mul_ne_zero (pow_ne_zero 3 h1) h,
  convert (lem2_1 feq h2 (-t ^ 2)).symm using 2,
  rw [add_neg_self, zero_add, mul_assoc, neg_sq, bit0, ← two_mul, pow_mul],
  rw [neg_sq, neg_mul, ← sq, add_neg_cancel_right]
end

private lemma lem2_5 (h : ∃ t : ℝ, t < 2⁻¹ ∧ good f t) : ∃ c : ℝ, f c = f 0 ∧ c ≠ 0 :=
begin
  rcases h with ⟨t, h, c, h0, h1⟩,
  rcases eq_or_ne t 0 with rfl | h2,
  use c; rw [and_iff_left h0, ← h1, mul_zero],
  rcases lem1_3 h with ⟨x, h3⟩,
  use c ^ 3 * (t + x ^ 2 + x * t ^ 2); split,
  replace feq := lem2_1 feq h1 x,
  rwa [add_right_comm (t ^ 2), h3, mul_zero] at feq,
  refine mul_ne_zero (pow_ne_zero 3 h0) _,
  intros h4; rw add_eq_zero_iff_eq_neg at h4,
  rw [sq, ← mul_add, h4, mul_neg, neg_add_eq_zero, mul_left_comm,
      mul_right_eq_self₀, ← pow_succ, bit0, pow_bit1_eq_one_iff 1 t] at h3,
  rcases h3 with rfl | rfl,
  exact not_lt_of_le (by norm_num) h,
  rw [sq, zero_mul, zero_mul, add_zero, neg_zero] at h4,
  exact h2 h4
end

private lemma lem2_6 (h : ∃ t : ℝ, t ≠ 1 ∧ good f t) : ∃ c : ℝ, f c = f 0 ∧ c ≠ 0 :=
begin
  replace h : ∃ t : ℝ, t < 1 ∧ good f t :=
  begin
    rcases h with ⟨t, h, h0⟩,
    rw ne_iff_lt_or_gt at h,
    cases h with h h,
    exact ⟨t, h, h0⟩,
    use t⁻¹; split,
    exact inv_lt_one h,
    rcases h0 with ⟨c, h0, h1⟩,
    replace h := ne_of_gt (gt_trans h one_pos),
    use c * t; split,
    exact mul_ne_zero h0 h,
    rw [h1, mul_assoc, mul_inv_cancel h, mul_one]
  end,
  rcases h with ⟨t, h, h0⟩,
  cases lt_or_le t 2⁻¹ with h1 h1,
  exact lem2_5 feq ⟨t, h1, h0⟩,
  replace h1 : 0 < t := lt_of_lt_of_le (by norm_num) h1,
  obtain ⟨n, h2⟩ : ∃ n : ℕ, t ^ n < 2⁻¹ := exists_pow_lt_of_lt_one (inv_pos.mpr zero_lt_two) h,
  refine lem2_5 feq ⟨t ^ (4 ^ n), _, _⟩,
  { refine lt_trans _ h2,
    rw pow_lt_pow_iff_of_lt_one h1 h,
    exact nat.lt_pow_self (by norm_num) n },
  { clear h2; induction n with n n_ih,
    rwa [pow_zero, pow_one],
    rw [pow_succ', pow_mul],
    exact lem2_4 feq (pow_ne_zero _ (ne_of_gt h1)) n_ih }
end

/-- If f is not injective, then f is constant. -/
private lemma thm2 (h : ¬injective f) : f = const ℝ (f 0) :=
begin
  refine lem2_3 feq (lem2_2 feq _),
  simp only [injective, not_forall] at h,
  rcases h with ⟨a, b, h, h0⟩,
  rcases eq_or_ne b 0 with rfl | h1,
  exact ⟨a, h, h0⟩,
  apply lem2_6 feq,
  use a / b; split,
  intros h2; exact h0 (eq_of_div_eq_one h2),
  use b; rw [and_iff_right h1, mul_div_cancel' a h1, h]
end

end f_not_inj



section f_inj_f0_eq_0

variables {R : Type*} [comm_ring R] [is_domain R]
variables {f : ℝ → R} (feq : fn_eq f) (f_inj : injective f) (f0_eq_0 : f 0 = 0)
include feq f_inj f0_eq_0

private lemma lem3_1 (a b : ℝ) : (f a - f b) * f a * f b = f (b * a ^ 2) - f (a * b ^ 2) :=
begin
  replace feq := feq b a 0,
  rw [f0_eq_0, sub_zero, zero_sub, mul_neg, ← neg_mul, ← neg_mul, neg_sub] at feq,
  rw [feq, zero_pow zero_lt_two]; simp only [add_zero, zero_mul, mul_zero]
end

private lemma lem3_2 {a : ℝ} (h : a ≠ 0) : (f 1 - (f a + f (-a))) * f 1 = 1 :=
begin
  have h0 := lem3_1 feq f_inj f0_eq_0 1,
  simp only [one_pow, mul_one, one_mul] at h0,
  replace h0 : (f a - f (-a)) * ((f 1 - (f a + f (-a))) * f 1) = f a - f (-a) :=
  begin
    convert congr_arg2 has_sub.sub (h0 a) (h0 (-a)) using 1,
    ring,
    rw [neg_sq, sub_sub_sub_cancel_right]
  end,
  rw [mul_right_eq_self₀, sub_eq_zero] at h0,
  revert h0; refine (or_iff_left _).mp,
  intros h0,
  replace h0 := f_inj h0,
  rw eq_neg_self_iff at h0,
  exact h h0
end

private lemma lem3_3 (a : ℝ) : f (-a) = -f a :=
begin
  obtain ⟨C, h⟩ : ∃ C : R, ∀ b : ℝ, b ≠ 0 → f (-b) = C - f b :=
  begin
    use f 1 + f (-1); intros b h,
    rw eq_sub_iff_add_eq',
    replace h := lem3_2 feq f_inj f0_eq_0 h,
    have h0 := lem3_2 feq f_inj f0_eq_0 one_ne_zero,
    rw [← h0, mul_eq_mul_right_iff, sub_right_inj] at h,
    revert h; refine (or_iff_left _).mp,
    intros h,
    rw [h, mul_zero] at h0,
    exact zero_ne_one h0
  end,
  revert a; suffices : C = 0,
  { intros a,
    rcases eq_or_ne a 0 with rfl | h0,
    rw [neg_zero, f0_eq_0, neg_zero],
    rw [h a h0, this, zero_sub] },
  replace feq : ∀ a : ℝ, a ≠ 0 → a⁻¹ ≠ a → f a⁻¹ * f a = 1 :=
  begin
    intros a h0 h1,
    replace feq := lem3_1 feq f_inj f0_eq_0 a⁻¹ a,
    rwa [sq, ← mul_assoc, mul_inv_cancel h0, one_mul, sq, ← mul_assoc,
         inv_mul_cancel h0, one_mul, mul_assoc, mul_right_eq_self₀,
         sub_eq_zero, or_iff_left (λ h2, h1 (f_inj h2))] at feq
  end,
  have h0 := feq (-2) (by norm_num) (by norm_num),
  rwa [h 2 two_ne_zero, ← neg_inv, h 2⁻¹ (by norm_num), sub_mul,
       mul_sub (f 2⁻¹), feq 2 two_ne_zero (by norm_num), ← sub_add,
       add_left_eq_self, mul_comm, ← sub_mul, mul_eq_zero, sub_eq_zero] at h0,
  revert h0; refine (or_iff_right _).mp,
  rw ← h 2 two_ne_zero,
  intros h0; replace h0 := f_inj h0,
  revert h0; norm_num
end

private lemma lem3_4 : (f 1) ^ 2 = 1 :=
begin
  have h := lem3_2 feq f_inj f0_eq_0 one_ne_zero,
  rwa [lem3_3 feq f_inj f0_eq_0, add_neg_self, sub_zero, ← sq] at h
end

private lemma R2ne0 (f1_eq_1 : f 1 = 1) : (2 : R) ≠ 0 :=
begin
  intros h,
  rw [bit0, ← eq_neg_iff_add_eq_zero, ← f1_eq_1, ← lem3_3 feq f_inj f0_eq_0] at h,
  replace h := f_inj h,
  rw [eq_neg_iff_add_eq_zero, ← bit0] at h,
  exact two_ne_zero h
end

private lemma lem3_5 (f1_eq_1 : f 1 = 1) (a b : ℝ) : f (a * b) = f a * f b :=
begin
  revert a b; suffices : ∀ a b : ℝ, 0 ≤ a → f (a * b) = f a * f b,
  { intros a b,
    cases le_total 0 a with h h,
    exact this a b h,
    rw [← neg_le_neg_iff, neg_zero] at h,
    replace this := this _ b h,
    replace h := lem3_3 feq f_inj f0_eq_0,
    rwa [neg_mul, h, h, neg_mul, neg_inj] at this },
  suffices : ∀ a b : ℝ, f (a ^ 2 * b) = f a ^ 2 * f b,
  { intros a b h,
    have h0 := this (sqrt a) 1,
    rw [mul_one, f1_eq_1, sq_sqrt h, mul_one] at h0,
    replace this := this (sqrt a) b,
    rwa [← h0, sq_sqrt h] at this },
  intros a b,
  have h := lem3_1 feq f_inj f0_eq_0 a,
  replace h := congr_arg2 has_sub.sub (h b) (h (-b)),
  simp only [neg_sq, neg_mul, mul_neg, sub_sub_sub_cancel_right,
             sub_neg_eq_add, lem3_3 feq f_inj f0_eq_0] at h,
  rwa [← add_mul, ← add_mul, sub_add_add_cancel, ← two_mul, mul_assoc (2 : R), ← sq,
       mul_comm b, ← two_mul, mul_assoc, eq_comm, mul_eq_mul_left_iff] at h,
  exact (or_iff_left (R2ne0 feq f_inj f0_eq_0 f1_eq_1)).mp h
end

private lemma lem3_6 (f1_eq_1 : f 1 = 1) (a : ℝ) (n : ℕ) : f (a ^ n) = f a ^ n :=
begin
  induction n with n n_ih,
  rw [pow_zero, pow_zero, f1_eq_1],
  rw [pow_succ, pow_succ, lem3_5 feq f_inj f0_eq_0 f1_eq_1, n_ih]
end



variable f1_eq_1 : f 1 = 1
include f1_eq_1

private lemma lem3_7 {t : ℝ} (h : t ≠ 0) :
  f (t ^ 2 + t⁻¹) + f (t ^ 2 - t⁻¹) = f 2 - 2 + 2 * f t ^ 2 :=
begin
  revert t h,
  have fodd := lem3_3 feq f_inj f0_eq_0,
  have fmul := lem3_5 feq f_inj f0_eq_0 f1_eq_1,
  suffices : ∀ t : ℝ, t < 0 → f (t ^ 2 + t⁻¹) + f (t ^ 2 - t⁻¹) = f 2 - 2 + 2 * f t ^ 2,
  { intros t h,
    rw [ne_iff_lt_or_gt, gt_iff_lt, ← neg_neg_iff_pos] at h,
    cases h with h h,
    exact this t h,
    replace this := this (-t) h,
    rwa [neg_sq, ← neg_inv, fodd, neg_sq, add_comm, sub_neg_eq_add, ← sub_eq_add_neg] at this },
  intros t h,
  obtain ⟨x, h0⟩ := lem1_3 (lt_trans h (by norm_num)),
  replace feq := feq 1 t,
  conv at feq { find (_ = _) {
    rw [f1_eq_1, one_mul, one_mul, one_pow, mul_one, mul_one, add_right_comm t] } },
  have h1 : t + x ^ 2 = -x * t⁻¹ := by rw [eq_mul_inv_iff_mul_eq₀ (ne_of_lt h),
    mul_comm, mul_add, ← sq, ← add_eq_zero_iff_eq_neg, h0],
  rw add_eq_zero_iff_eq_neg at h0,
  have h2 := congr_arg2 has_sub.sub (feq (-x)) (feq x),
  rw [neg_sq, h0, h1, neg_add_self, f0_eq_0, zero_sub, sub_neg_eq_add, ← mul_add, ← two_mul,
      fmul, fmul, add_comm ((-x * _)), neg_mul, ← sub_eq_add_neg, ← mul_sub, fmul, fodd] at h2,
  replace h2 : (2 * f t ^ 2 - 2) * f x = (f (t⁻¹ + t ^ 2) + f (t ^ 2 - t⁻¹) - f 2) * f x :=
    by convert h2; ring,
  rw mul_eq_mul_right_iff at h2,
  cases h2 with h2 h2,
  rwa [add_comm t⁻¹, eq_sub_iff_add_eq', add_sub, add_sub_right_comm, eq_comm] at h2,
  rw ← f0_eq_0 at h2; replace h2 := f_inj h2,
  rw [h2, neg_zero, zero_mul, sq, zero_mul, add_zero] at h1,
  exfalso; exact ne_of_lt h h1
end

private lemma lem3_8 : ∀ t u : ℝ, 2 * f (t ^ 3 + u ^ 3) =
 (f 2 - 2) * (f t ^ 2 * f u + f u ^ 2 * f t) + 2 * (f u ^ 3 + f t ^ 3) :=
begin
  have fodd := lem3_3 feq f_inj f0_eq_0,
  have fpow := lem3_6 feq f_inj f0_eq_0 f1_eq_1,
  have fmul := lem3_5 feq f_inj f0_eq_0 f1_eq_1,

  suffices : ∀ t u : ℝ, f (t ^ 3 + u ^ 3) + f (u ^ 3 - t ^ 3)
    = (f 2 - 2) * f t ^ 2 * f u + 2 * f u ^ 3,
  { intros t u,
    replace this := congr_arg2 has_add.add (this t u) (this u t),
    rw [← neg_sub, fodd, ← sub_eq_add_neg, sub_add_add_cancel, add_comm (u ^ 3)] at this,
    rw [two_mul, this, add_add_add_comm, ← mul_add, mul_assoc, mul_assoc, ← mul_add] },
    
  intros t u,
  rcases eq_or_ne t 0 with rfl | h,
  rw [f0_eq_0, zero_pow three_pos, zero_add, sub_zero, ← two_mul,
      fpow, zero_pow two_pos, mul_zero, zero_mul, zero_add],
  rcases eq_or_ne u 0 with rfl | h0,
  rw [f0_eq_0, zero_pow three_pos, add_zero, zero_sub, fodd,
      add_neg_self, zero_pow three_pos, ← add_mul, mul_zero],
  have h1 := congr_arg (* (f (t ^ 2 * u)))
    (lem3_7 feq f_inj f0_eq_0 f1_eq_1 (div_ne_zero h0 h)),
  simp only [add_mul] at h1,
  rw [← fmul, ← fmul, mul_assoc, ← fpow, ← fmul] at h1,
  field_simp at h1,
  rwa [fmul, fpow, ← mul_assoc, mul_comm (t ^ 2) u, ← mul_assoc, ← pow_succ', ← pow_succ,
       mul_div_cancel _ (pow_ne_zero 2 h), ← pow_succ', add_comm (u ^ _) (t ^ _), fpow] at h1
end

private lemma lem3_9 : f 2 = 2 ∨ f (nat_root 3 2) = 2 :=
begin
  have fpow := lem3_6 feq f_inj f0_eq_0 f1_eq_1,
  have fneg1 : f (-1) = -1 := by rw [lem3_3 feq f_inj f0_eq_0, f1_eq_1],
  have h := lem3_8 feq f_inj f0_eq_0 f1_eq_1 (nat_root 3 2) (-1),
  rw [← fpow (nat_root 3 2) 3, pow_nat_root_self_bit1, neg_pow_bit1, one_pow, fneg1,
      mul_comm, bit0, ← sub_eq_add_neg, add_sub_cancel, f1_eq_1, ← sub_eq_zero] at h,
  set D := f (nat_root 3 2),
  replace h : (f 2 - 2) * (D - 2) * (D + 1) = 0 := by rw ← h; ring,
  rw [mul_eq_zero, add_eq_zero_iff_eq_neg] at h,
  cases h with h h,
  rwa [mul_eq_zero, sub_eq_zero, sub_eq_zero] at h,
  replace h := congr_arg (λ x, x ^ 3) h,
  dsimp only [D] at h,
  rw [← fpow, pow_nat_root_self_bit1, neg_pow_bit1, one_pow, ← fneg1] at h,
  replace h := f_inj h,
  exfalso; revert h; norm_num
end

private theorem thm3_1 (f2_eq_2 : f 2 = 2) : ∃ φ : ℝ →+* R, f = (φ : ℝ → R) :=
begin
  refine ⟨⟨f, f1_eq_1, lem3_5 feq f_inj f0_eq_0 f1_eq_1, f0_eq_0, _⟩, rfl⟩,
  intros x y,
  have h := lem3_8 feq f_inj f0_eq_0 f1_eq_1 (nat_root 3 x) (nat_root 3 y),
  have fpow := lem3_6 feq f_inj f0_eq_0 f1_eq_1,
  rw [f2_eq_2, sub_self, zero_mul, ← fpow, ← fpow, pow_nat_root_self_bit1,
      pow_nat_root_self_bit1, zero_add, mul_eq_mul_left_iff] at h,
  cases h with h h,
  rw [h, add_comm],
  exfalso; exact R2ne0 feq f_inj f0_eq_0 f1_eq_1 h
end

private theorem thm3_2 (froot2_eq_2 : f (nat_root 3 2) = 2) : ∃ φ : ℝ →+* R, f = λ x, φ x ^ 3 :=
begin
  have fpow := lem3_6 feq f_inj f0_eq_0 f1_eq_1,
  use λ x, f (nat_root 3 x),
  rw [nat_root_bit1_one, f1_eq_1],
  intros x y,
  rw [nat_root_bit1_mul, lem3_5 feq f_inj f0_eq_0 f1_eq_1],
  rw [nat_root_bit1_zero, f0_eq_0],
  swap,
  rw ring_hom.coe_mk; funext x,
  rw [← fpow, pow_nat_root_self_bit1 1], 
  replace froot2_eq_2 : f 2 - 2 = 2 * 3 :=
    by rw [← pow_nat_root_self_bit1 1 2, fpow, froot2_eq_2]; norm_num,
  have h : ∀ x : ℝ, (λ x, f (nat_root 3 x)) (-x) = -(λ x, f (nat_root 3 x)) x :=
    λ x, by dsimp only []; rw [nat_root_bit1_neg 1 x, lem3_3 feq f_inj f0_eq_0],
  refine g_sum_cube_eq_sum_g_cube (λ x y, _) h,
  replace h := lem3_8 feq f_inj f0_eq_0 f1_eq_1 (nat_root 3 x) (nat_root 3 y),
  rw [pow_nat_root_self_bit1, pow_nat_root_self_bit1, froot2_eq_2,
      mul_assoc, ← mul_add, mul_eq_mul_left_iff] at h,
  cases h with h h,
  rw [← fpow, pow_nat_root_self_bit1, h]; ring,
  exfalso; exact R2ne0 feq f_inj f0_eq_0 f1_eq_1 h
end

end f_inj_f0_eq_0

end results



/- Final solution -/
theorem final_solution_general {R : Type*} [comm_ring R] [is_domain R] (f : ℝ → R) : fn_eq f ↔
  (∃ C : R, f = const ℝ C) ∨
  ((∃ (φ : ℝ →+* R) (C : R), f = φ + const ℝ C) ∨
   (∃ (φ : ℝ →+* R) (C : R), f = (λ x, φ x ^ 3) + const ℝ C)) ∨
  ((∃ (φ : ℝ →+* R) (C : R), f = -φ + const ℝ C) ∨
   (∃ (φ : ℝ →+* R) (C : R), f = -(λ x, φ x ^ 3) + const ℝ C)) :=
begin
  split,
  { intros feq,
    by_cases h : injective f,
    swap,
    left; use (f 0); exact thm2 feq h,
    right; set g := f - const ℝ (f 0) with hg,
    rw [← lem1_1 (-f 0), ← pi.const_neg, ← sub_eq_add_neg, ← hg] at feq,
    replace h : injective g := λ x y h0,
      by simp only [g, pi.sub_apply, const_apply, sub_left_inj] at h0; exact h h0,
    have h0 : g 0 = 0 := by rw [hg, pi.sub_apply, const_apply, sub_self],
    have h1 := lem3_4 feq h h0,
    rw sq_eq_one_iff at h1,
    cases h1 with h1 h1,
    { left; cases lem3_9 feq h h0 h1 with h2 h2,
      left; rcases thm3_1 feq h h0 h1 h2 with ⟨φ, h3⟩; use [φ, (f 0)],
      rw [← h3, hg, sub_add_cancel],
      right; rcases thm3_2 feq h h0 h1 h2 with ⟨φ, h3⟩; use [φ, (f 0)],
      rw [← h3, hg, sub_add_cancel] },
    { right; clear_value g; subst hg,
      set g := -(f - const ℝ (f 0)) with hg,
      rw [← lem1_2, ← hg] at feq,
      replace h : injective g := λ x y h2,
        by rw [hg, pi.neg_apply, pi.neg_apply, neg_inj] at h2; exact h h2,
      rw [← neg_eq_zero, ← pi.neg_apply (f - _) 0, ← hg] at h0,
      rw [eq_neg_iff_add_eq_zero, ← neg_eq_iff_add_eq_zero, ← pi.neg_apply (f - _) 1, ← hg] at h1,
      cases lem3_9 feq h h0 h1 with h2 h2,
      left; rcases thm3_1 feq h h0 h1 h2 with ⟨φ, h3⟩; use [φ, (f 0)],
      rw [← h3, hg, neg_neg, sub_add_cancel],
      right; rcases thm3_2 feq h h0 h1 h2 with ⟨φ, h3⟩; use [φ, (f 0)],
      rw [← h3, hg, neg_neg, sub_add_cancel] } },
  suffices : ∀ φ : ℝ →+* R, fn_eq φ ∧ fn_eq (λ x, φ x ^ 3),
  { rintros (⟨C, rfl⟩ | (⟨φ, C, rfl⟩ | ⟨φ, C, rfl⟩) | (⟨φ, C, rfl⟩ | ⟨φ, C, rfl⟩)),
    rw [← zero_add (const ℝ C), lem1_1],
    intros a b c; simp only [pi.zero_apply, sub_zero, mul_zero],
    all_goals { rw lem1_1 },
    exacts [(this φ).left, (this φ).right, lem1_2.mpr (this φ).left, lem1_2.mpr (this φ).right] },
  { intros φ; split,
    all_goals { intros a b c, simp only [map_add, map_mul, map_pow], ring } }
end

/-- Final solution, case char(R) ≠ 0 -/
theorem final_solution_char_ne_0 {R : Type*} [comm_ring R] [is_domain R]
  (p : ℕ) [fact (p ≠ 0)] [char_p R p] (f : ℝ → R) : fn_eq f ↔ ∃ C : R, f = const ℝ C :=
begin
  rw final_solution_general,
  apply or_iff_left,
  simp only [is_empty.exists_iff, or_false],
  exact not_false
end

/-- Final solution, case R = ℝ -/
theorem final_solution_real (f : ℝ → ℝ) : fn_eq f ↔ (∃ C : ℝ, f = const ℝ C) ∨
  ((∃ C : ℝ, f = id + const ℝ C) ∨ (∃ C : ℝ, f = (λ x, x ^ 3) + const ℝ C)) ∨
  ((∃ C : ℝ, f = -id + const ℝ C) ∨ (∃ C : ℝ, f = -(λ x, x ^ 3) + const ℝ C)) :=
  by simp only [final_solution_general, unique.exists_iff]; congr'

end IMO2021A8
end IMOSL
