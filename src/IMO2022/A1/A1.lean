import algebra.order.ring.defs algebra.group_power.order

/-! # IMO 2022 A1 -/

namespace IMOSL
namespace IMO2022A1

variables {R : Type*} [linear_ordered_comm_ring R]

lemma main_ineq_alt_form {a b c : R} (h : b ^ 2 + a * c ≤ a + c) :
  b ^ 2 - 1 ≤ (1 - a) * (c - 1) :=
  (sub_le_sub_right (le_sub_right_of_add_le h) 1).trans_eq $
    by rw [add_sub_assoc, ← one_sub_mul, add_comm, add_sub_assoc,
      ← neg_sub 1 a, ← sub_eq_add_neg, ← mul_sub_one]

lemma main_ineq_imp_of_pos {a b c : R} (h : 0 ≤ a) (h0 : 1 < b) (h1 : 1 ≤ c)
  (h2 : b ^ 2 + a * c ≤ a + c) : 2 * (b - 1) < c - 1 :=
by calc
_ < (b + 1) * (b - 1) : mul_lt_mul_of_pos_right (add_lt_add_right h0 1) (sub_pos_of_lt h0)
... = b ^ 2 - 1 : (sq_sub_sq b 1).symm.trans $ congr_arg _ (one_pow 2)
... ≤ (1 - a) * (c - 1) : main_ineq_alt_form h2
... ≤ c - 1 : mul_le_of_le_one_left (sub_nonneg_of_le h1) (sub_le_self 1 h)

lemma no_consecutive_one_lt {a b c d : R} (h : 0 ≤ a) (h0 : 1 < b) (h1 : 1 < c) (h2 : 0 ≤ d)
  (h3 : b ^ 2 + a * c ≤ a + c) (h4 : c ^ 2 + b * d ≤ b + d) : false :=
have c ^ 2 + d * b ≤ d + b := (congr_arg _ $ mul_comm d b).trans_le $ h4.trans_eq (add_comm b d),
(add_lt_add (main_ineq_imp_of_pos h h0 h1.le h3) (main_ineq_imp_of_pos h2 h1 h0.le this)).asymm $
  (lt_two_mul_self $ add_pos (sub_pos_of_lt h1) (sub_pos_of_lt h0)).trans_eq $
  (mul_add _ _ _).trans (add_comm _ _)





/-- Final solution -/
theorem final_solution {a : ℕ → R} (h : ∀ i, 0 ≤ a i)
  (h0 : ∀ i, a (i + 1) ^ 2 + a i * a (i + 2) ≤ a i + a (i + 2))
  (N : ℕ) : a (N + 2) ≤ 1 :=
le_of_not_lt $ λ h1, (lt_or_le 1 $ a (N + 1)).elim
  ---- `1 < a_{N + 1}`
  (λ h2, no_consecutive_one_lt (h N) h2 h1 (h $ N + 3) (h0 N) (h0 $ N + 1)) $
λ h2, (lt_or_le 1 $ a (N + 3)).elim
  ---- `1 < a_{N + 3}`
  (λ h3, no_consecutive_one_lt (h $ N + 1) h1 h3 (h $ N + 4) (h0 $ N + 1) (h0 $ N + 2))
  ---- `a_{N + 1}, a_{N + 3} ≤ 1`
  (λ h3, ((sub_pos_of_lt $ (one_lt_sq_iff_one_lt_abs _).mpr $ h1.trans_le $
      le_abs_self _).trans_le $ main_ineq_alt_form $ h0 $ N + 1).not_le
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg_of_le h2) (sub_nonpos_of_le h3)))

end IMO2022A1
end IMOSL
