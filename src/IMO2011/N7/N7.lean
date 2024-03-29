import
  number_theory.padics.padic_integers
  data.nat.choose.dvd
  field_theory.finite.basic

/-! # IMO 2011 N7 -/

namespace IMOSL
namespace IMO2011N7

open finset

variables {p : ℕ} [fact p.prime]

noncomputable def S (a : ℚ_[p]) := (Ico 1 p).sum (λ i, a ^ i / i)



private lemma padic_norm_int_eq_one_iff_not_dvd (k : ℤ) : ‖(k : ℚ_[p])‖ = 1 ↔ ¬(p : ℤ) ∣ k :=
  by rw ← padic_norm_e.norm_int_lt_one_iff_dvd;
    exact (has_le.le.not_lt_iff_eq $ padic_norm_e.norm_int_le_one k).symm

private lemma padic_binom_norm {k : ℕ} (h : 0 < k) (h0 : k < p) :
  ‖(p : ℚ_[p]) / k + (-1) ^ k * p.choose k‖ ≤ p ^ (-2 : ℤ) :=
begin
  ---- Reduce to `p^2 ∣ p + (-1)^k k C(p, k)`
  have h1 : (k : ℚ_[p]) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt h),
  rw [div_add' _ _ _ h1, norm_div, mul_assoc, ← nat.cast_mul],
  replace h1 : ‖(k : ℚ_[p])‖ = 1 :=
    by rw [← int.cast_coe_nat, padic_norm_int_eq_one_iff_not_dvd, int.coe_nat_dvd];
      exact nat.not_dvd_of_pos_of_lt h h0,    
  rw [h1, div_one, ← nat.cast_two, ← int.cast_coe_nat, ← int.cast_coe_nat (_ * _),
      ← int.cast_one, ← int.cast_neg, ← int.cast_pow, ← int.cast_mul, ← int.cast_add,
      padic_norm_e.norm_int_le_pow_iff_dvd],

  ---- Induction on `k`
  clear h1; rw [← nat.succ_le_iff, le_iff_exists_add'] at h,
  rcases h with ⟨k, rfl⟩; induction k with k h,
  rw [zero_add, mul_one, pow_one, nat.choose_one_right, neg_one_mul, add_neg_self],
  exact dvd_zero _,
  replace h0 := lt_trans (k + 1).lt_succ_self h0,
  replace h := h h0; revert h; refine (dvd_iff_dvd_of_dvd_sub _).mp,
  rw [add_sub_add_left_eq_sub, pow_succ _ k.succ, neg_one_mul,
      neg_mul, sub_neg_eq_add, ← mul_add, ← nat.cast_add],
  refine dvd_mul_of_dvd_right (int.coe_nat_dvd.mpr _) _,
  rw [nat.choose_succ_right_eq p k.succ, ← mul_add, nat.add_sub_of_le (le_of_lt h0), sq],
  exact mul_dvd_mul_right ((fact.out p.prime).dvd_choose_self (ne_of_gt k.succ_pos) h0) p
end

private lemma ultra_norm_add_le {t : ℝ} {a b : ℚ_[p]}
  (h : ‖a‖ ≤ t) (h0 : ‖b‖ ≤ t) : ‖a + b‖ ≤ t :=
  le_trans (padic_norm_e.nonarchimedean _ _) (max_le h h0)

private lemma ultra_norm_sum_le {ι : Type*} [decidable_eq ι] {f : ι → ℚ_[p]} {s : finset ι}
  {t : ℝ} (h : 0 ≤ t) (h0 : ∀ i : ι, i ∈ s → ‖f i‖ ≤ t) : ‖s.sum f‖ ≤ t :=
begin
  induction s using finset.induction with j s h1 h2,
  exact le_of_eq_of_le norm_zero h,
  simp_rw [mem_insert, forall_eq_or_imp] at h0,
  rw sum_insert h1; exact ultra_norm_add_le h0.1 (h2 h0.2)
end

private lemma special_identity {p : ℕ} (h : odd p) {R : Type*} [comm_ring R] (a : R) :
  a ^ p - (a - 1) ^ p - 1 = (Ico 1 p).sum (λ i, (-a) ^ i * p.choose i) :=
begin
  rw nat.odd_iff at h,
  have h0 : 1 ≤ p := by rw ← h; exact nat.mod_le p 2,
  rw [sum_Ico_eq_add_neg _ h0, sum_range_one, pow_zero, p.choose_zero_right, one_mul,
      nat.cast_one, ← sub_eq_add_neg, sub_left_inj, sub_eq_iff_eq_add, sub_eq_add_neg,
      add_pow, sum_range_succ, ← add_assoc, ← sum_add_distrib, nat.sub_self,
      pow_zero, mul_one, p.choose_self, nat.cast_one, mul_one, self_eq_add_left],
  refine sum_eq_zero (λ x h1, _),
  rw [← add_mul, neg_pow, mul_comm (a ^ x), ← add_mul, mul_assoc],
  apply mul_eq_zero_of_left; clear h0 a,

  rw [mem_range, lt_iff_exists_add] at h1,
  rcases h1 with ⟨c, -, rfl⟩,
  rw [nat.add_sub_cancel_left, neg_one_pow_eq_pow_mod_two],
  cases nat.mod_two_eq_zero_or_one x with h0 h0,
  rw [h0, pow_zero, add_eq_zero_iff_neg_eq, eq_comm],
  rw [nat.add_mod, h0, zero_add, nat.mod_mod] at h,
  rw [neg_one_pow_eq_pow_mod_two, h, pow_one],
  rw [h0, pow_one, neg_add_eq_zero, eq_comm],
  rw [← nat.odd_iff, nat.odd_iff_not_even] at h h0,
  rw [nat.even_add, not_iff, iff_true_left h0] at h,
  exact h.neg_one_pow
end

private lemma S_equiv_mod_p_sq (h : odd p) {a : ℚ_[p]} (h0 : ‖a‖ ≤ 1) :
  ‖(p : ℚ_[p]) * S a + (a ^ p - (a - 1) ^ p - 1)‖ ≤ p ^ (-2 : ℤ) :=
begin
  rw [special_identity h, S, mul_sum, ← sum_add_distrib],
  refine ultra_norm_sum_le (zpow_nonneg p.cast_nonneg _) (λ i h1, _),
  rw [mul_div_left_comm, ← mul_neg_one, mul_pow, mul_assoc, ← mul_add, norm_mul, norm_pow],
  rw mem_Ico at h1; exact mul_le_of_le_one_of_le_of_nonneg
    (pow_le_one i (norm_nonneg a) h0) (padic_binom_norm h1.1 h1.2) (norm_nonneg _)
end







/- Final solution -/
theorem final_solution (h : odd p) : ‖S (3 : ℚ_[p]) + S 4 - 3 * S 2‖ < 1 :=
begin
  ---- Reduce to showing that an expression equivalent to `(2^p - 2)^2` has norm at most `p^{-2}`
  set T := λ (z : ℤ), z ^ p - (z - 1) ^ p - 1,
  have h0 : ∀ z : ℤ, ‖(p : ℚ_[p]) * S z + T z‖ ≤ p ^ (-2 : ℤ) :=
    λ z, by simp_rw [T, int.cast_sub, int.cast_pow, int.cast_sub, int.cast_one];
      exact S_equiv_mod_p_sq h (padic_norm_e.norm_int_le_one z),
  replace h : ‖((-3 : ℤ) : ℚ_[p])‖ ≤ 1 := padic_norm_e.norm_int_le_one (-3),
  replace h := mul_le_of_le_one_of_le_of_nonneg h (h0 2) (norm_nonneg _); rw ← norm_mul at h,
  replace h0 := ultra_norm_add_le (ultra_norm_add_le (h0 3) (h0 4)) h; clear h,
  rw [add_add_add_comm, mul_add, ← mul_add, add_add_add_comm, mul_left_comm,
      ← mul_add, ← int.cast_mul, ← int.cast_add, ← int.cast_add] at h0,
  simp_rw [int.cast_neg, int.cast_bit1, int.cast_bit0, int.cast_one] at h0,
  rw [sub_eq_add_neg, ← neg_mul]; revert h0,
  suffices : ‖((T 3 + T 4 + (-3) * T 2 : ℤ) : ℚ_[p])‖ ≤ p ^ (-(2 : ℕ) : ℤ),
  { rw ← norm_neg at this,
    intros h; replace h := ultra_norm_add_le h this,
    replace this : 0 < (p : ℝ) := nat.cast_pos.mpr (fact.out p.prime).pos,
    rw [add_neg_cancel_right, norm_mul, padic_norm_e.norm_p, inv_mul_le_iff this,
        mul_comm (p : ℝ), ← zpow_add_one₀ (ne_of_gt this)] at h,
    change (-2 + 1 : ℤ) with (-1 : ℤ) at h,
    rw [zpow_neg_one, ← padic_norm_e.norm_p] at h,
    exact lt_of_le_of_lt h padic_norm_e.norm_p_lt_one },

  ---- Reduce to `T(3) + T(4) - 3 T(2) = (2^p - 2)^2`
  rw [padic_norm_e.norm_int_le_pow_iff_dvd, nat.cast_pow, neg_mul, ← sub_eq_add_neg],
  suffices : T 3 + T 4 - 3 * T 2 = (2 ^ p - 2) ^ 2,
    rw this; apply pow_dvd_pow_of_dvd;
      rw [← zmod.int_coe_eq_int_coe_iff_dvd_sub, int.cast_pow, int.cast_two, zmod.pow_card],
  
  ---- Prove that `T(3) + T(4) - 3 T(2) = (2^p - 2)^2`
  change T 3 with (3 : ℤ) ^ p - 2 ^ p - 1,
  change T 4 with (2 * 2 : ℤ) ^ p - 3 ^ p - 1,
  change T 2 with (2 : ℤ) ^ p - 1 ^ p - 1,
  rw [one_pow, mul_pow, ← sq, sub_add_sub_comm, sub_add_sub_cancel'],
  generalize : (2 : ℤ) ^ p = q,
  rw [sub_eq_iff_eq_add, sub_sub q, ← bit0, sq, sq, ← add_mul, bit1,
      ← add_assoc, sub_add_cancel, add_one_mul, sub_sub, sub_eq_iff_eq_add,
      add_assoc, sub_add_add_cancel, ← mul_two, ← mul_add, sub_add_cancel]
end

end IMO2011N7
end IMOSL
