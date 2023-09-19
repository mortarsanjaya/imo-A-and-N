import algebra.big_operators.basic

/-! # IMO 2017 A7 -/

namespace IMOSL
namespace IMO2017A7

variables {b : ℕ → ℤ} (b_pos : ∀ n : ℕ, 0 < b n)
include b_pos

def a : ℕ → ℤ
| 0 := 0
| 1 := 1
| (n + 2) := a (n + 1) * b (n + 1) + a n * ite (b n = 1) 1 (-1)



open finset

lemma main_equality :
  ∀ n : ℕ, a b_pos n.succ = a b_pos n * (b n - 1) + (range n).sum (λ i, a b_pos i * |b i - 2|) + 1
| 0 := self_eq_add_left.mpr $ congr_arg2 has_add.add (zero_mul _) (sum_range_zero _)
| (n+1) := begin
  rw [a, mul_sub_one, ← add_sub_right_comm, add_sub_assoc, add_assoc,
    add_right_inj, main_equality, sum_range_succ_comm, ← sub_sub,
    add_sub_add_right_eq_sub, sub_add_cancel, ← mul_sub],
  refine congr_arg (has_mul.mul $ a b_pos n)
    ((eq_or_ne (b n) 1).elim (λ h, by rw h; refl) (λ h, _)),
  have h0 : 1 < b n := lt_of_le_of_ne (b_pos n) h.symm,
  rw [int.lt_iff_add_one_le, ← sub_nonneg] at h0,
  rw [if_neg h, bit0, abs_of_nonneg h0, sub_sub_sub_cancel_left, sub_add_cancel']
end

lemma a_and_sum_nonneg :
  ∀ n : ℕ, 0 ≤ a b_pos n ∧ 0 ≤ (range n).sum (λ i, a b_pos i * |b i - 2|)
| 0 := ⟨le_refl 0, le_refl 0⟩
| (n+1) := let h := a_and_sum_nonneg n in
  ⟨le_of_eq_of_le' (main_equality b_pos n).symm $
    int.add_nonneg (int.add_nonneg (int.mul_nonneg h.1 $ int.sub_nonneg_of_le $
        int.add_one_le_of_lt $ b_pos n) h.2) int.one_nonneg,
  (int.add_nonneg h.2 $ int.mul_nonneg h.1 $ abs_nonneg _).trans_eq (sum_range_succ _ n).symm⟩

lemma a_plus_sum_ge :
  ∀ n : ℕ, (n : ℤ) ≤ a b_pos n + (range n).sum (λ i, a b_pos i * |b i - 2|)
| 0 := le_refl 0
| (n+1) := begin
    refine (add_le_add_right (a_plus_sum_ge n) 1).trans _,
    rw [sum_range_succ_comm, ← add_assoc, add_right_comm,
        add_le_add_iff_right, main_equality b_pos n, add_right_comm,
        add_le_add_iff_right, add_right_comm, ← mul_add],
    have h := a_and_sum_nonneg b_pos n,
    refine (le_mul_of_one_le_right h.1 _).trans (le_add_of_nonneg_right h.2),
    rw [← sub_le_iff_le_add', ← neg_sub, sub_sub],
    exact neg_le_abs_self (b n - 2)
  end



/-- Final solution -/
theorem final_solution (n : ℕ) : (n : ℤ) ≤ a b_pos n ∨ (n : ℤ) ≤ a b_pos n.succ :=
begin
  cases n with _ n,
  exact or.inl (le_refl 0),
  have h0 : ∀ n : ℕ, 0 ≤ a b_pos n := λ n, (a_and_sum_nonneg _ n).1,
  refine (int.add_one_le_of_lt $ b_pos n).lt_or_eq.imp (λ h, _) (λ h, _),

  -- `b_n ≥ 2 → n + 1 ≤ a_{n + 1}`
  rw [main_equality, nat.cast_succ, add_le_add_iff_right],
  exact (a_plus_sum_ge b_pos n).trans (add_le_add_right
    (le_mul_of_one_le_right (h0 n) (int.le_sub_one_of_lt h)) _),

  -- `b_n = 1 → n + 1 ≤ a_n`
  rw [nat.cast_succ, main_equality, add_le_add_iff_right],
  refine le_trans _ (le_add_of_nonneg_left $
    int.mul_nonneg (h0 n.succ) (int.le_sub_one_of_lt $ b_pos n.succ)),
  rw [sum_range_succ_comm, ← h, bit0, zero_add, sub_add_cancel', abs_neg, abs_one, mul_one],
  exact a_plus_sum_ge b_pos n
end

end IMO2017A7
end IMOSL
