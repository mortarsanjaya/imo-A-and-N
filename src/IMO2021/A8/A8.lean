import
  data.real.basic
  data.real.golden_ratio
  algebra.algebra.basic
  extra.real_nat_root
  extra.real_hom.semifield_char0_hom
  extra.real_hom.real_additive_End
  extra.real_quadratic_sol

/-! # IMO 2021 A8, Generalized Version -/

open function real
open_locale classical

namespace IMOSL
namespace IMO2021A8

def fn_eq {R : Type*} [comm_ring R] [is_domain R] (f : ℝ → R) :=
  ∀ a b c : ℝ, (f(a) - f(b)) * (f(b) - f(c)) * (f(c) - f(a))
    = f(a * b ^ 2 + b * c ^ 2 + c * a ^ 2) - f(b * a ^ 2 + c * b ^ 2 + a * c ^ 2)



namespace extra

lemma g_sum_zero_of_g_cube_sum_zero {R S} [add_comm_monoid R]
    [comm_ring S] [is_domain S] (char_ne_3 : ring_char S ≠ 3)
    {g : R → S} (h : ∀ x y z : R, x + y + z = 0 → (g x + g y) ^ 3 + g z ^ 3 = 0) :
  ∀ x y z : R, x + y + z = 0 → g x + g y + g z = 0 :=
begin
  have three_ne_zero : (3 : S) ≠ 0 :=
    λ h0, char_ne_3 (char_p.ring_char_of_prime_eq_zero nat.prime_three (by simp; exact h0)),

  ---- First off we prove that the following result suffices:
  ---- For any t, u, v ∈ S, if (t + u)^3 + v^3 = (u + v)^3 + t^3,
  ----   then either t + u + v = 0, u = 0, or v = t.
  revert g h,
  suffices : ∀ t u v : S, (t + u) ^ 3 + v ^ 3 = 0 → (u + v) ^ 3 + t ^ 3 = 0 →
    t + u + v = 0 ∨ u = 0 ∨ v = t,
  { intros g h x y z sum_eq_0,
    have hxyz := h x y z sum_eq_0,
    rw [add_assoc, add_comm] at sum_eq_0,
    have hyzx := h y z x sum_eq_0,
    rw [add_assoc, add_comm] at sum_eq_0,
    have hzxy := h z x y sum_eq_0,
    clear h sum_eq_0,
    rcases this _ _ _ hzxy hxyz with h | h | h,
    rw [add_comm, ← add_assoc, h],
    rw [h, zero_pow zero_lt_three, add_zero] at hyzx,
    rw [h, zero_add]; exact pow_eq_zero hyzx,
    rcases this _ _ _ hxyz hyzx with h0 | h0 | h0,
    exact h0,
    rw [h0, zero_pow zero_lt_three, add_zero] at hzxy,
    rw [h0, add_zero, add_comm]; exact pow_eq_zero hzxy,
    rw [h, h0] at hxyz ⊢; clear h h0 hzxy hyzx,
    rw [← two_mul, mul_pow, ← add_one_mul, mul_eq_zero, or_comm] at hxyz,
    cases hxyz with h h,
    rw [pow_eq_zero h, add_zero, add_zero],
    replace h : (3 : S) ^ 2 = 0 := by rw ← h; norm_num,
    exfalso; exact three_ne_zero (pow_eq_zero h) },

  intros t u v h h0,
  rw [← h0, ← sub_eq_zero] at h; clear h0,
  replace h : -((t + u + v) * (u * (v - t)) * 3) = 0 := by rw ← h; ring,
  rwa [neg_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero,
       sub_eq_zero, or_iff_left three_ne_zero] at h
end

end extra




section results

variables {R : Type*} [comm_ring R] [is_domain R]

/-- Useful definition for the case where f is not injective -/
private def good (f : ℝ → R) (t : ℝ) := ∃ c : ℝ, c ≠ 0 ∧ f (c * t) = f c

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



section f_not_inj

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

private lemma lem2_2 (h : ∀ x : ℝ, f (-x) = f x) : f = const ℝ (f 0) :=
begin
  ext x,
  suffices : ∃ y : ℝ, x = 2 * golden_ratio * y ^ 3,
  { cases this with y h0,
    replace feq := feq y (-y) (golden_ratio * y),
    rw [h, sub_self, zero_mul, zero_mul, eq_comm, sub_eq_zero, neg_sq, eq_comm] at feq,
    convert feq; clear feq; ring_nf,
    rw [h0, add_one_mul, ← sq, gold_sq, add_right_comm, add_sub_cancel, ← two_mul],
    rw [add_one_mul (-golden_ratio), neg_mul, add_assoc, ← sq, gold_sq, neg_add_self, zero_mul] },
  use nat_root 3 (x / (2 * golden_ratio)),
  rw [pow_nat_root_self_bit1, mul_div_cancel' x (mul_ne_zero two_ne_zero gold_ne_zero)]
end

private lemma lem2_3 {t : ℝ} (t_good : good f t) : good f t⁻¹ :=
begin
  rcases eq_or_ne t 0 with rfl | h,
  rwa inv_zero,
  rcases t_good with ⟨c, h0, h1⟩,
  use c * t; split,
  exact mul_ne_zero h0 h,
  rw [h1, mul_assoc, mul_inv_cancel h, mul_one]
end

private lemma lem2_4 {t : ℝ} (t_ne_0 : t ≠ 0) (t_good : good f t) : good f (t ^ 4) :=
begin
  rcases t_good with ⟨c, c_ne_0, h⟩,
  replace feq := feq (c * t) c (- c * t ^ 2),
  rw [h, sub_self, zero_mul, zero_mul, eq_comm, sub_eq_zero] at feq,
  ring_nf at feq,
  use t * c ^ 3; split,
  exact mul_ne_zero t_ne_0 (pow_ne_zero 3 c_ne_0),
  rw [mul_comm, ← mul_assoc, ← pow_succ', feq]
end

private lemma lem2_5 (h : ∃ t : ℝ, (t ≤ 0 ∨ 2 < t) ∧ good f t) : good f 0 :=
begin
  rcases h with ⟨t, h, t_good⟩,
  rcases eq_or_ne t 0 with rfl | t_ne_0,
  exact t_good,
  replace h : ∃ u : ℝ, u ^ 2 + t ^ 2 * u + t = 0 :=
  begin
    apply extra.exists_root_quadratic,
    cases h with h h,
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos zero_le_four h) (sq_nonneg _),
    rw [← pow_mul, mul_two, ← bit0, pow_succ', mul_le_mul_right (lt_trans zero_lt_two h)],
    refine le_trans _ (pow_le_pow_of_le_left zero_le_two (le_of_lt h) 3),
    norm_num
  end,
  rcases h with ⟨u, h0⟩,
  rcases t_good with ⟨c, c_ne_0, h⟩,
  use ((t + u ^ 2) * t + u) * c ^ 3,
  rw [mul_zero, and_comm]; split,
  { replace feq := feq (c * t) c (c * u),
    rw [h, sub_self, zero_mul, zero_mul, eq_comm, sub_eq_zero] at feq,
    ring_nf at feq,
    rwa [add_one_mul, add_comm, ← add_assoc, mul_assoc, mul_comm u, ← sq, h0, zero_mul] at feq },
  { refine mul_ne_zero _ (pow_ne_zero 3 c_ne_0),
    intros h1,
    rw [add_right_comm, add_eq_zero_iff_eq_neg, add_comm] at h0,
    rw [h0, neg_mul, neg_add_eq_zero, mul_right_comm, mul_left_eq_self₀, or_comm] at h1,
    rcases h1 with rfl | h1,
    rw [zero_pow zero_lt_two, add_zero, mul_zero, neg_zero] at h0,
    exact t_ne_0 h0,
    replace h1 := congr_arg (nat_root 3) h1,
    rw [← pow_succ', ← bit1, nat_root_pow_self_bit1, nat_root_bit1_one] at h1,
    rw [h1, one_pow, one_mul, ← add_eq_zero_iff_eq_neg] at h0,
    replace h1 : 4 * (1 + u ^ 2 + u) = (2 * u + 1) ^ 2 + 3 := by ring,
    rw [h0, mul_zero, eq_comm, add_eq_zero_iff_eq_neg] at h1,
    replace h0 : (0 : ℝ) ≤ -3 := by rw ← h1; exact sq_nonneg _,
    exact not_lt_of_le h0 (by norm_num) }
end

private lemma lem2_6 (h : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ good f t) : ∃ t : ℝ, 2 < t ∧ good f t :=
begin
  rcases h with ⟨t, t_gt_0, t_lt_1, h⟩,
  replace h : ∀ n : ℕ, ∃ c : ℝ, c ≠ 0 ∧ f (c * t ^ (4 ^ n)) = f c :=
  begin
    intros n; induction n with n n_ih,
    rcases h with ⟨c, h, h0⟩,
    use c,
    rw [and_iff_right h, pow_zero, pow_one, h0],
    rw [pow_succ', pow_mul],
    refine lem2_4 feq (pow_ne_zero _ (ne_of_gt t_gt_0)) n_ih
  end,

  obtain ⟨n, h0⟩ : ∃ n : ℕ, t ^ (4 ^ n) < 2⁻¹ :=
  begin
    obtain ⟨n, h0⟩ : ∃ n : ℕ, t ^ n < 2⁻¹ :=
      exists_pow_lt_of_lt_one (inv_pos.mpr zero_lt_two) t_lt_1,
    use n; refine lt_trans _ h0,
    rw pow_lt_pow_iff_of_lt_one t_gt_0 t_lt_1,
    refine nat.lt_pow_self (by norm_num) n
  end,

  replace t_gt_0 := pow_pos t_gt_0 (4 ^ n),
  replace h := h n,
  rcases h with ⟨c, h, h1⟩,
  set u := t ^ 4 ^ n with hu,
  use u⁻¹; split,
  rwa lt_inv zero_lt_two t_gt_0,
  use c * u; split,
  exact mul_ne_zero h (ne_of_gt t_gt_0),
  rw [h1, mul_assoc, mul_inv_cancel (ne_of_gt t_gt_0), mul_one]
end

private lemma lem2_7 (h : ∃ t : ℝ, t ≠ 1 ∧ good f t) : good f 0 :=
begin
  rcases h with ⟨t, h, h0⟩,
  cases le_or_lt t 0 with h1 h1,
  exact lem2_5 feq ⟨t, (by left; exact h1), h0⟩,
  rw ne_iff_lt_or_gt at h,
  cases h with h h,
  rcases lem2_6 feq ⟨t, h1, h, h0⟩ with ⟨u, h2, h3⟩,
  exact lem2_5 feq ⟨u, (by right; exact h2), h3⟩,
  rw [← inv_one, gt_iff_lt, inv_lt zero_lt_one h1] at h,
  rw ← inv_pos at h1,
  rcases lem2_6 feq ⟨t⁻¹, h1, h, (lem2_3 feq h0)⟩ with ⟨u, h2, h3⟩,
  exact lem2_5 feq ⟨u, (by right; exact h2), h3⟩
end

private lemma lem2_8 {a b : ℝ} (h : f a = f b) (h0 : a ≠ b) : ∃ c : ℝ, c ≠ 0 ∧ f c = f 0 :=
begin
  rcases eq_or_ne b 0 with rfl | h1,
  exact ⟨a, h0, h⟩,
  suffices : good f 0,
  { rcases this with ⟨c, h1, h2⟩,
    use c; rw [and_iff_right h1, ← h2, mul_zero] },
  apply lem2_7 feq,
  use a / b; split,
  intros h2; exact h0 (eq_of_div_eq_one h2),
  use b; rw [and_iff_right h1, mul_div_cancel' a h1, h]
end

private theorem thm2 (h : ¬injective f) : f = const ℝ (f 0) :=
begin
  simp only [injective, not_forall] at h,
  rcases h with ⟨a, b, h, h0⟩,
  rcases lem2_8 feq h h0 with ⟨c, h1, h2⟩,
  exact lem2_2 feq (lem2_1 feq h1 h2)
end

end f_not_inj



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

private lemma lem3_6 (f1_eq_1 : f 1 = 1) : (2 : R) ≠ 0 :=
begin
  intros h,
  replace h : f 1 = f (-1) :=
    by rw [lem3_5 feq f_inj f0_eq_0, f1_eq_1, eq_neg_iff_add_eq_zero, ← bit0, h],
  replace h := f_inj h,
  rw [eq_neg_iff_add_eq_zero, ← bit0] at h,
  exact two_ne_zero h
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
  exact lem3_6 feq f_inj f0_eq_0 f1_eq_1
end

private theorem thm3_3 (f1_eq_1 : f 1 = 1) (a : ℝ) (n : ℕ) : f (a ^ n) = f a ^ n :=
begin
  induction n with n n_ih,
  rw [pow_zero, pow_zero, f1_eq_1],
  rw [pow_succ, pow_succ, thm3_2 feq f_inj f0_eq_0 f1_eq_1, n_ih]
end




variable f1_eq_1 : f 1 = 1
include f1_eq_1

private lemma lem4_1 (u v : ℝ) : (f u - 1) * (f v - 1) * (f (u * v) - 1)
  = f ((u * v) ^ 2 + (u + v)) - f ((u + v) * (u * v) + 1) :=
begin
  have f_mul := thm3_2 feq f_inj f0_eq_0 f1_eq_1,
  rcases eq_or_ne v 0 with rfl | h,
  rw [mul_zero, f0_eq_0, zero_sub, mul_neg_one, mul_neg_one, neg_neg,
      zero_pow zero_lt_two, zero_add, add_zero, mul_zero, zero_add, f1_eq_1],
  have h0 := feq v (u * v) 1,
  rw [f_mul, ← one_sub_mul, mul_comm _ (f v), one_pow, mul_one, one_mul, one_mul, mul_one] at h0,
  have h1 : v * (u * v) ^ 2 + u * v + v ^ 2 = v * ((u * v) ^ 2 + (u + v)) := by ring,
  have h2 : u * v * v ^ 2 + (u * v) ^ 2 + v = v * ((u + v) * (u * v) + 1) := by ring,
  rw [h1, h2] at h0; clear h1 h2,
  rw [f_mul, f_mul, f1_eq_1, ← mul_sub, mul_assoc, mul_assoc, mul_eq_mul_left_iff, ← f_mul] at h0,
  cases h0 with h0 h0,
  convert h0 using 1; ring,
  exfalso; exact h (f_inj (by rw [h0, f0_eq_0]))
end

private lemma lem4_2 (x y : ℝ) : 2 * (f (x ^ 2) - 1) = 
  (f (x ^ 2 + y) + f (x ^ 2 - y)) - (f (1 + x * y) + f (1 - x * y)) :=
begin
  revert x y; suffices : ∀ x y : ℝ, x ≤ 0 → 2 * (f (x ^ 2) - 1) = 
    (f (x ^ 2 + y) + f (x ^ 2 - y)) - (f (1 + x * y) + f (1 - x * y)),
  { intros x y,
    cases le_total x 0 with h h,
    exact this x y h,
    rw ← neg_nonpos at h,
    replace this := this _ y h,
    rwa [neg_sq, neg_mul, sub_neg_eq_add, ← sub_eq_add_neg, add_comm (f (1 - _))] at this },
  intros x y x_le_0,
  obtain ⟨u, v, h, h0⟩ : ∃ u v : ℝ, u + v = y ∧ u * v = x := extra.exists_add_eq_mul_eq y x
      (le_trans (mul_nonpos_of_nonneg_of_nonpos zero_le_four x_le_0) (sq_nonneg y)),
  have h1 := lem4_1 feq f_inj f0_eq_0 f1_eq_1 u v,
  rw [h, h0] at h1,
  have h2 := lem4_1 feq f_inj f0_eq_0 f1_eq_1 (-u) (-v),
  rw [neg_mul_neg, ← neg_add, h, h0, lem3_5 feq f_inj f0_eq_0,
      lem3_5 feq f_inj f0_eq_0, ← neg_add', ← neg_add', neg_mul_neg] at h2,
  replace h1 := congr_arg2 (λ x y, x + y) h1 h2; clear h2,
  simp only [] at h1,
  rw [sub_add_sub_comm, ← sub_eq_add_neg, ← add_mul] at h1,
  convert h1 using 1; clear h1,
  ring_nf; rw [mul_assoc, ← thm3_2 feq f_inj f0_eq_0 f1_eq_1,
    mul_comm v u, ← h0, thm3_3 feq f_inj f0_eq_0 f1_eq_1]; ring,
  rw [sub_right_inj, mul_comm, add_comm (1 : ℝ), sub_eq_add_neg, add_comm (1 : ℝ), neg_mul]
end

private lemma lem4_3 (t : ℝ) : f (t + 1) - f (t - 1) = (f 2 - 2) * f (nat_root 3 t ^ 2) + 2 :=
begin
  rcases eq_or_ne t 0 with rfl | h,
  rw [zero_add, zero_sub, lem3_5 feq f_inj f0_eq_0, f1_eq_1, sub_neg_eq_add,
      nat_root_bit1_zero, zero_pow zero_lt_two, f0_eq_0, mul_zero, zero_add, bit0],
  set u := nat_root 3 t with hu,
  have h0 := lem4_2 feq f_inj f0_eq_0 f1_eq_1 u⁻¹ u,
  rw [inv_mul_cancel (nat_root_bit1_ne_zero 1 h), sub_self, f0_eq_0, add_zero, ← bit0,
      eq_sub_iff_add_eq, mul_sub_one, sub_add, sub_eq_add_neg, neg_sub] at h0,
  replace h0 := congr_arg (λ x, f (u ^ 2) * x) h0; simp only [] at h0,
  have fmul := thm3_2 feq f_inj f0_eq_0 f1_eq_1,
  rw [mul_add, mul_add, mul_left_comm, ← fmul, ← fmul, ← fmul, mul_add, mul_sub (u ^ 2),
      ← mul_pow, mul_inv_cancel (nat_root_bit1_ne_zero 1 h), one_pow, eq_comm] at h0,
  convert h0 using 1,
  rw ← pow_succ'; change 2 + 1 with 3,
  rw [pow_nat_root_self_bit1, add_comm, ← neg_sub t 1, lem3_5 feq f_inj f0_eq_0, sub_eq_add_neg],
  rw [f1_eq_1, mul_one, add_comm, mul_comm]
end

private theorem thm4 (f2_eq_2 : f 2 = 2) : ∃ φ : ℝ →+* R, f = (φ : ℝ → R) :=
begin
  have fmul := thm3_2 feq f_inj f0_eq_0 f1_eq_1,
  use f,
  exact f1_eq_1,
  exact fmul,
  exact f0_eq_0,
  swap,
  rw ring_hom.coe_mk,
  intros x y,
  rcases eq_or_ne y 0 with rfl | h,
  rw [f0_eq_0, add_zero, add_zero],
  have h0 := lem4_3 feq f_inj f0_eq_0 f1_eq_1 (2 * x / y + 1),
  rw [f2_eq_2, sub_self, zero_mul, zero_add, add_sub_cancel, add_assoc, ← bit0] at h0,
  replace h0 := congr_arg (λ x, x * f y) h0; simp only [] at h0,
  rwa [sub_mul, ← fmul, ← fmul, add_mul, div_mul_cancel _ h, sub_eq_iff_eq_add, ← mul_add,
       fmul, fmul, f2_eq_2, ← mul_add, add_comm (f y), mul_eq_mul_left_iff, or_iff_left] at h0,
  exact lem3_6 feq f_inj f0_eq_0 f1_eq_1
end



variable f2_ne_2 : f 2 ≠ 2
include f2_ne_2

private lemma lem5_1 (t : ℝ) : f (nat_root 3 (t + 1) ^ 2) + f (nat_root 3 (t - 1) ^ 2)
  = f (nat_root 3 2) * f (nat_root 3 t ^ 2) + 2 :=
begin
  have X := lem4_3 feq f_inj f0_eq_0 f1_eq_1,
  have h := congr_arg2 (λ x y, x + y) (X (t + 1)) (X (t - 1)); simp only [] at h,
  rw [add_sub_cancel, sub_add_cancel, sub_add_sub_cancel,
      sub_sub, add_assoc, ← bit0, add_add_add_comm, ← mul_add] at h,
  replace X := congr_arg (λ x, f 2 * x) (X (t / 2)); simp only [] at X,
  have fmul := thm3_2 feq f_inj f0_eq_0 f1_eq_1,
  rw [mul_sub, ← fmul, ← fmul, mul_add_one, mul_sub_one, mul_div_cancel' t two_ne_zero, h] at X,
  clear h,
  rw [mul_add (f 2), ← mul_two, ← eq_sub_iff_add_eq, add_sub_assoc, ← sub_mul,
      mul_left_comm, ← mul_add, mul_eq_mul_left_iff, sub_eq_zero, or_iff_left f2_ne_2] at X,
  rw [X, ← fmul, ← fmul, ← nat_root_bit1_pow, ← nat_root_bit1_pow,
      ← nat_root_bit1_mul, nat_root_bit1_left_mul]; congr' 3,
  rw [div_pow, pow_succ, mul_assoc, mul_div_cancel'],
  exact pow_ne_zero 2 two_ne_zero
end

private lemma lem5_2 : f (nat_root 3 2) = 2 :=
begin
  have h := lem5_1 feq f_inj f0_eq_0 f1_eq_1 f2_ne_2 1,
  rw [sub_self, nat_root_bit1_zero, zero_pow zero_lt_two, f0_eq_0, add_zero, nat_root_bit1_one,
      one_pow, f1_eq_1, mul_one, thm3_3 feq f_inj f0_eq_0 f1_eq_1, ← bit0, ← sub_eq_zero] at h,
  set u := f (nat_root 3 2),
  replace h : (u + 1) * (u - 2) = 0 := by rw ← h; ring,
  rwa [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg, or_comm] at h,
  cases h with h h,
  exact h,
  rw [← f1_eq_1, ← lem3_5 feq f_inj f0_eq_0] at h,
  replace h := congr_arg (λ x, x ^ 3) (f_inj h),
  simp only [one_pow, neg_pow_bit1, pow_nat_root_self_bit1] at h,
  rw ← add_eq_zero_iff_eq_neg at h,
  exfalso; exact three_ne_zero h
end

private lemma lem5_3 (t u : ℝ) :
  f (t + u) - f (t - u) = 2 * (3 * f (nat_root 3 t ^ 2) * f (nat_root 3 u) + f u) :=
begin
  have f2_eq_8 : f 2 = 2 * 3 + 2 := by rw [← pow_nat_root_self_bit1 1 2,
    thm3_3 feq f_inj f0_eq_0 f1_eq_1, lem5_2 feq f_inj f0_eq_0 f1_eq_1 f2_ne_2]; norm_num,
  rcases eq_or_ne u 0 with rfl | h,
  rw [add_zero, sub_zero, sub_self, nat_root_bit1_zero, f0_eq_0, mul_zero, add_zero, mul_zero],
  have fmul := thm3_2 feq f_inj f0_eq_0 f1_eq_1,
  have h0 := congr_arg (λ x, x * f u) (lem4_3 feq f_inj f0_eq_0 f1_eq_1 (t / u)),
  simp only [] at h0,
  rw [sub_mul, ← fmul, ← fmul, add_one_mul, sub_one_mul, div_mul_cancel t h] at h0,
  rw [h0, f2_eq_8, add_sub_cancel]; clear h0,
  rw [mul_assoc, ← mul_add_one, mul_assoc, add_one_mul, mul_assoc, mul_assoc]; congr' 3,
  rw [← fmul, ← fmul, ← nat_root_bit1_pow, ← nat_root_bit1_pow, ← nat_root_bit1_mul, mul_comm,
      nat_root_bit1_left_mul, mul_comm, pow_succ' u, ← mul_assoc]; congr' 3,
  rw [div_pow, div_mul_cancel _ (pow_ne_zero 2 h)]
end

private lemma lem5_4 (t u : ℝ) : f (nat_root 3 (t + u)) ^ 3
  = (f (nat_root 3 t) + f (nat_root 3 u)) ^ 3 :=
begin
  have fpow := thm3_3 feq f_inj f0_eq_0 f1_eq_1,
  rw [← fpow, pow_nat_root_self_bit1 1],
  have h := lem5_3 feq f_inj f0_eq_0 f1_eq_1 f2_ne_2,
  replace h := congr_arg2 (λ x y, x + y) (h t u) (h u t); simp only [] at h,
  rw [← neg_sub u t, lem3_5 feq f_inj f0_eq_0, sub_neg_eq_add, add_add_sub_cancel,
      add_comm u t, ← two_mul, ← mul_add, mul_eq_mul_left_iff,
      or_iff_left (lem3_6 feq f_inj f0_eq_0 f1_eq_1)] at h,
  nth_rewrite 2 ← pow_nat_root_self_bit1 1 u at h,
  nth_rewrite 3 ← pow_nat_root_self_bit1 1 t at h,
  rw [fpow, fpow, fpow, fpow] at h,
  rw h; ring
end

private lemma lem5_5 (t u : ℝ) : f (nat_root 3 (t + u)) = (f (nat_root 3 t) + f (nat_root 3 u)) :=
begin
  revert t u,
  suffices : ∀ t u v : ℝ, t + u + v = 0 →
    f (nat_root 3 t) + f (nat_root 3 u) + f (nat_root 3 v) = 0,
  { intros t u,
    replace this := this t u (-(t + u)) (by rw add_neg_self),
    rwa [nat_root_bit1_neg, lem3_5 feq f_inj f0_eq_0,
         ← sub_eq_add_neg, sub_eq_zero, eq_comm] at this },

  apply extra.g_sum_zero_of_g_cube_sum_zero,
  { intros char_eq_3,
    have h := lem5_4 feq f_inj f0_eq_0 f1_eq_1 f2_ne_2 1 1,
    rw [← thm3_3 feq f_inj f0_eq_0 f1_eq_1, pow_nat_root_self_bit1,
        nat_root_bit1_one, f1_eq_1, ← bit0] at h,
    apply f2_ne_2,
    rw [h, ← sub_eq_zero]; norm_num,
    rw ring_char.eq_iff at char_eq_3,
    have cast3 : ↑(3 : ℕ) = (3 : R) := by simp only [nat.cast_bit1, nat.cast_one],
    resetI; rw [bit0, ← cast3, char_p.cast_eq_zero R (3 : ℕ), add_zero] },

  { intros x y z h,
    rw add_eq_zero_iff_eq_neg at h,
    rw [← lem5_4 feq f_inj f0_eq_0 f1_eq_1 f2_ne_2, h, nat_root_bit1_neg,
        lem3_5 feq f_inj f0_eq_0, neg_pow_bit1, neg_add_self] }
end

private theorem thm5 : ∃ φ : ℝ →+* R, f = λ x, φ x ^ 3 :=
begin
  use λ x, f (nat_root 3 x),
  rw [nat_root_bit1_one, f1_eq_1],
  intros x y,
  rw [nat_root_bit1_mul, thm3_2 feq f_inj f0_eq_0 f1_eq_1],
  rw [nat_root_bit1_zero, f0_eq_0],
  swap,
  rw ring_hom.coe_mk; funext x,
  rw [← thm3_3 feq f_inj f0_eq_0 f1_eq_1, pow_nat_root_self_bit1 1],
  exact lem5_5 feq f_inj f0_eq_0 f1_eq_1 f2_ne_2
end

end f_inj_f0_eq_0

end results



/-- Final solution -/
theorem final_solution_general {R : Type*} [comm_ring R] [is_domain R] (f : ℝ → R) : fn_eq f ↔
  (∃ C : R, f = const ℝ C) ∨ ∃ (φ : ℝ →+* R) (C : R),
   ((f = φ + const ℝ C) ∨ (f = (λ x, φ x ^ 3) + const ℝ C)) ∨
   ((f = -φ + const ℝ C) ∨ (f = -(λ x, φ x ^ 3) + const ℝ C)) :=
begin
  split,
  { intros feq,
    by_cases h : injective f,
    swap,
    left; use (f 0); exact thm2 feq h,
    replace feq := lem1_1 feq (-f 0),
    replace h : injective (f + const ℝ (-f 0)) := λ x y h0,
      by simp only [pi.add_apply, const_apply, add_left_inj] at h0; exact h h0,
    set g := f + const ℝ (-f 0) with hg,
    have h0 : g 0 = 0 := by simp only [g, pi.add_apply, const_apply, add_right_neg],
    have h1 := thm3_1 feq h h0,
    rw [sq_eq_one_iff] at h1,
    right; cases h1 with h1 h1,
    { cases eq_or_ne (g 2) 2 with h2 h2,
      rcases thm4 feq h h0 h1 h2 with ⟨φ, h3⟩,
      use [φ, (f 0)]; left; left,
      rw [← h3, hg, add_assoc, pi.const_add (-f 0), neg_add_self, pi.const_zero, add_zero],
      rcases thm5 feq h h0 h1 h2 with ⟨φ, h3⟩,
      use [φ, (f 0)]; left; right,
      rw [← h3, hg, add_assoc, pi.const_add (-f 0), neg_add_self, pi.const_zero, add_zero] },
    { clear_value g; subst hg,
      set g := -(f + const ℝ (-f 0)) with hg,
      replace feq := lem1_2 feq,
      replace h : injective g := λ x y h2,
        by rw [hg, pi.neg_apply, pi.neg_apply, neg_inj] at h2; exact h h2,
      nth_rewrite 2 ← neg_zero at h0,
      rw [eq_neg_iff_eq_neg, eq_comm, ← pi.neg_apply (f + _) 0] at h0,
      rw [eq_neg_iff_eq_neg, eq_comm, ← pi.neg_apply (f + _) 1] at h1,
      rw ← hg at feq h0 h1,
      cases eq_or_ne (g 2) 2 with h2 h2,
      rcases thm4 feq h h0 h1 h2 with ⟨φ, h3⟩,
      use [φ, (f 0)]; right; left,
      rw [← h3, hg, neg_neg, add_assoc, pi.const_add (-f 0),
          neg_add_self, pi.const_zero, add_zero],
      rcases thm5 feq h h0 h1 h2 with ⟨φ, h3⟩,
      use [φ, (f 0)]; right; right,
      rw [← h3, hg, neg_neg, add_assoc, pi.const_add (-f 0),
          neg_add_self, pi.const_zero, add_zero] } },
  { rintros (⟨C, rfl⟩ | ⟨φ, C, h⟩),
    simp [fn_eq],
    suffices h0 : fn_eq φ ∧ fn_eq (λ x, φ x ^ 3),
    { cases h0 with h0 h1,
      rcases h with (rfl | rfl) | (rfl | rfl),
      exacts [lem1_1 h0 C, lem1_1 h1 C, lem1_1 (lem1_2 h0) C, lem1_1 (lem1_2 h1) C] },
    split; intros a b c; simp only [map_add, map_pow, map_mul]; ring },
end

/-- Final solution, case char(R) ≠ 0 -/
theorem final_solution_char_ne_0 {R : Type*} [comm_ring R] [is_domain R]
    (p : ℕ) [fact (p ≠ 0)] [char_p R p] (f : ℝ → R) : fn_eq f ↔ ∃ C : R, f = const ℝ C :=
begin
  rw final_solution_general,
  apply or_iff_left,
  rw is_empty.exists_iff,
  exact not_false
end

/-- Final solution, case R = ℝ -/
theorem final_solution_real (f : ℝ → ℝ) : fn_eq f ↔ (∃ C : ℝ, f = const ℝ C) ∨ ∃ C : ℝ,
   ((f = id + const ℝ C) ∨ (f = (λ x, x ^ 3) + const ℝ C)) ∨
   ((f = -id + const ℝ C) ∨ (f = -(λ x, x ^ 3) + const ℝ C)) :=
begin
  rw final_solution_general,
  apply or_congr_right',
  rw unique.exists_iff,
  simp only [default, ring_hom.coe_one, id.def]
end

end IMO2021A8
end IMOSL
