import data.real.basic analysis.special_functions.pow

/-!
# Natural root in ℝ

We define the `n`th root in ℝ where `n` is a natural number.
For `n` even, we define the `n`th root of a negative real number `x` as `-(x^(1/n))`.
It has useful properties especially when `n` is odd.

TODO:
1. Prove properties when `n` is a `bit0`.
2. Prove more properties in general.
-/

open real function
open_locale classical

namespace real

/-- odd-function `n`th root in ℝ -/
noncomputable def nat_root (n : ℕ) (x : ℝ) := ite (0 ≤ x) (x ^ (n : ℝ)⁻¹) (- ((-x) ^ (n : ℝ)⁻¹))

lemma nat_root_pow_self_bit1 (n : ℕ) (x : ℝ) : nat_root (bit1 n) (x ^ (bit1 n)) = x :=
begin
  simp only [nat_root, pow_bit1_nonneg_iff],
  by_cases h : 0 ≤ x,
  rw if_pos h; exact pow_nat_rpow_nat_inv h (nat.bit1_ne_zero n),
  rw [if_neg h, ← neg_pow_bit1, pow_nat_rpow_nat_inv _ (nat.bit1_ne_zero n), neg_neg],
  rw [← lt_iff_not_le, ← neg_pos] at h,
  exact le_of_lt h
end

lemma pow_nat_root_self_bit1 (n : ℕ) (x : ℝ) : (nat_root (bit1 n) x) ^ (bit1 n) = x :=
begin
  dsimp only [nat_root],
  by_cases h : 0 ≤ x,
  rw if_pos h; exact rpow_nat_inv_pow_nat h (nat.bit1_ne_zero n),
  rw [if_neg h, neg_pow_bit1, rpow_nat_inv_pow_nat _ (nat.bit1_ne_zero n), neg_neg],
  rw [← lt_iff_not_le, ← neg_pos] at h,
  exact le_of_lt h
end

lemma pow_bit1_inj (n : ℕ) : injective (λ x : ℝ, x ^ (bit1 n)) :=
begin
  intros x y h; simp only [] at h,
  rw [← nat_root_pow_self_bit1 n x, h, nat_root_pow_self_bit1]
end

lemma nat_root_bit1_inj (n : ℕ) : injective (nat_root (bit1 n)) :=
  λ x y h, by rw [← pow_nat_root_self_bit1 n x, h, pow_nat_root_self_bit1]

lemma nat_root_bit1_mul (n : ℕ) (x y : ℝ) :
    nat_root (bit1 n) (x * y) = nat_root (bit1 n) x * nat_root (bit1 n) y :=
  pow_bit1_inj n (by simp only [mul_pow, pow_nat_root_self_bit1])

lemma nat_root_bit1_inv (n : ℕ) (x : ℝ) : nat_root (bit1 n) x⁻¹ = (nat_root (bit1 n) x)⁻¹ :=
  pow_bit1_inj n (by simp only [inv_pow, pow_nat_root_self_bit1])

lemma nat_root_bit1_one (n : ℕ) : nat_root (bit1 n) 1 = 1 :=
  pow_bit1_inj n (by simp only [pow_nat_root_self_bit1, one_pow])

lemma nat_root_bit1_zero (n : ℕ) : nat_root (bit1 n) 0 = 0 :=
  pow_bit1_inj n (by simp only [pow_nat_root_self_bit1, zero_pow (nat.zero_lt_bit1 n)])

lemma nat_root_bit1_neg (n : ℕ) (x : ℝ) : nat_root (bit1 n) (-x) = -(nat_root (bit1 n) x) :=
  pow_bit1_inj n (by simp only [pow_nat_root_self_bit1, neg_pow_bit1])

lemma nat_root_bit1_pow (n : ℕ) (x : ℝ) (k : ℕ) :
  nat_root (bit1 n) (x ^ k) = nat_root (bit1 n) x ^ k :=
begin
  induction k with k k_ih,
  rw [pow_zero, pow_zero, nat_root_bit1_one],
  rw [pow_succ, nat_root_bit1_mul, k_ih, pow_succ]
end

lemma nat_root_bit1_left_mul (n : ℕ) (x y : ℝ) :
    x * nat_root (bit1 n) y = nat_root (bit1 n) (x ^ (bit1 n) * y) :=
  by rw [nat_root_bit1_mul, nat_root_pow_self_bit1]

lemma nat_root_bit1_ne_zero (n : ℕ) {x : ℝ} (h : x ≠ 0) : nat_root (bit1 n) x ≠ 0 :=
  by contrapose! h; apply nat_root_bit1_inj; rw [h, nat_root_bit1_zero]

end real
