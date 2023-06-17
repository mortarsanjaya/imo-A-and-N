import algebra.geom_sum

/-! # IMO 2007 A3 -/

namespace IMOSL
namespace IMO2007A3

open finset

variables {F : Type*} [linear_ordered_field F]

lemma easy_ineq (x : F) : 0 ≤ (1 + x ^ 2) / (1 + x ^ 4) :=
  div_nonneg (add_nonneg zero_le_one $ sq_nonneg x)
    (add_nonneg zero_le_one $ pow_bit0_nonneg x 2)

lemma sum_easy_ineq (x : F) (S : finset ℕ) : 
  0 ≤ S.sum (λ i, (1 + x ^ (2 * i.succ)) / (1 + x ^ (4 * i.succ))) :=
  sum_nonneg $ λ i _, by rw [mul_comm, pow_mul, mul_comm, pow_mul]; exact easy_ineq _

lemma main_ineq {x : F} (h : 0 < x) (h0 : x ≠ 1) : (1 + x ^ 2) / (1 + x ^ 4) < x⁻¹ :=
begin
  rw [inv_eq_one_div, div_lt_div_iff (add_pos one_pos $ pow_pos h 4) h, one_mul, ← sub_pos],
  refine lt_of_lt_of_eq (_ : 0 < (x ^ 3 - 1) * (x - 1)) (by ring),
  have h1 : 3 ≠ 0 := nat.succ_ne_zero 2,
  rw ne_iff_lt_or_gt at h0; cases h0 with h0 h0,
  exact mul_pos_of_neg_of_neg (sub_neg.mpr $ pow_lt_one (le_of_lt h) h0 h1) (sub_neg.mpr h0),
  exact mul_pos (sub_pos.mpr $ one_lt_pow h0 h1) (sub_pos.mpr h0)
end

lemma sum_main_ineq {x : F} (h : 0 < x) (h0 : x < 1) {n : ℕ} (h1 : 0 < n) :
  (range n).sum (λ i, (1 + x ^ (2 * i.succ)) / (1 + x ^ (4 * i.succ)))
    < (x⁻¹ ^ n - 1) / (1 - x) :=
begin
  conv_lhs { congr, skip, funext, rw [mul_comm, pow_mul, mul_comm, pow_mul] },
  refine lt_of_lt_of_eq (sum_lt_sum_of_nonempty ⟨0, mem_range.mpr h1⟩ $ λ i _,
    main_ineq (pow_pos h _) $ ne_of_lt $ pow_lt_one (le_of_lt h) h0 i.succ_ne_zero) _,
  conv_lhs { congr, skip, funext, rw [← inv_pow, pow_succ] },
  rw [← mul_sum, geom_sum_eq (inv_ne_one.mpr $ ne_of_lt h0),
      mul_div_left_comm, ← inv_div, ← div_eq_mul_inv],
  refine congr_arg (has_div.div _) _,
  rw [div_eq_iff (inv_ne_zero $ ne_of_gt h), one_sub_mul, mul_inv_cancel (ne_of_gt h)]
end

lemma lt_one_of_pow_add {x y : F} (h : 0 < x)
  {n : ℕ} (h0 : x ^ n + y ^ n = 1) : y < 1 :=
  lt_of_not_le $ λ h1, ne_of_lt (add_lt_add_of_lt_of_le (pow_pos h n)
    (one_le_pow_of_one_le h1 n)) $ (zero_add 1).trans h0.symm





/-- Final solution -/
theorem final_solution {x y : F} (h : 0 < x) (h0 : 0 < y) {n : ℕ} (h1 : x ^ n + y ^ n = 1) :
  (range n).sum (λ i, (1 + x ^ (2 * i.succ)) / (1 + x ^ (4 * i.succ)))
    * (range n).sum (λ i, (1 + y ^ (2 * i.succ)) / (1 + y ^ (4 * i.succ)))
    < 1 / ((1 - x) * (1 - y)) :=
begin
  cases n.eq_zero_or_pos with h2 h2,
  rw [h2, pow_zero, pow_zero, add_right_eq_self] at h1,
  exact absurd h1 one_ne_zero,
  refine lt_of_lt_of_eq (mul_lt_mul''
    (sum_main_ineq h (lt_one_of_pow_add h0 $ (add_comm _ _).trans h1) h2)
    (sum_main_ineq h0 (lt_one_of_pow_add h h1) h2) (sum_easy_ineq _ _) (sum_easy_ineq _ _)) _,
  rw div_mul_div_comm; refine congr_arg2 has_div.div _ rfl,
  replace h2 : ∀ a : F, 0 < a → a ^ n ≠ 0 := λ a h2, ne_of_gt (pow_pos h2 n),
  rw [inv_pow, inv_pow, sub_one_mul, mul_sub_one, ← sub_add, add_left_eq_self,
      sub_sub, sub_eq_zero, inv_add_inv (h2 x h) (h2 y h0), h1, one_div, mul_inv]
end

end IMO2007A3
end IMOSL
