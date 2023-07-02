import algebra.big_operators.multiset.basic data.nat.parity

/-! # IMO 2013 N2 (P1) -/

namespace IMOSL
namespace IMO2013N2

open multiset

/-- Some notation hiding: The original problem reads as `∀ k, good k (2 ^ k - 1)`. -/
def good (k c : ℕ) := ∀ n : ℕ, 0 < n →
  ∃ S : multiset ℕ, (S.card = k ∧ ∀ m : ℕ, m ∈ S → 0 < m) ∧
    (n + c : ℚ) / n = (S.map $ λ m : ℕ, (m + 1 : ℚ) / m).prod

/-- Base case. -/
theorem good_zero_zero : good 0 0 :=
  λ n h, ⟨0, ⟨card_zero, λ m h, absurd h $ not_mem_zero m⟩,
    by rw [multiset.map_zero, prod_zero, nat.cast_zero, add_zero];
      exact div_self (ne_of_gt $ nat.cast_pos.mpr h)⟩

/-- Induction step, presented in a more general setting. -/
theorem good_succ_bit1_of_good {k c : ℕ} (h : good k c) : good (k + 1) (2 * c + 1) :=
  λ n h0, 
begin
  rcases n.even_or_odd' with ⟨t, rfl | rfl⟩,
  
  ---- `n = 2t`
  { have X := pos_of_mul_pos_right h0 (nat.zero_le 2),
    rcases h t X with ⟨T, ⟨h1, h2⟩, h3⟩,
    refine ⟨(2 * t + 2 * c) ::ₘ T, ⟨(card_cons _ _).trans (congr_arg nat.succ h1),
      λ m h4, (mem_cons.mp h4).elim (λ h4, (nat.add_pos_left h0 _).trans_eq h4.symm) (h2 m)⟩, _⟩,
    rw [map_cons, prod_cons, ← h3, ← nat.cast_add, ← nat.cast_add, ← add_assoc,
        ← mul_add, nat.cast_succ, nat.cast_mul, nat.cast_mul, nat.cast_two,
        ← div_div _ (2 : ℚ) ↑(t + c), div_mul_div_cancel, div_div],
    exact ne_of_gt (nat.cast_pos.mpr $ nat.add_pos_left X c) },

  ---- `n = 2t + 1`
  { have X := t.succ_pos,
    rcases h (t + 1) X with ⟨T, ⟨h1, h2⟩, h3⟩,
    refine ⟨(2 * t + 1) ::ₘ T, ⟨(card_cons _ _).trans (congr_arg nat.succ h1),
      λ m h4, (mem_cons.mp h4).elim (λ h4, (2 * t).succ_pos.trans_eq h4.symm) (h2 m)⟩, _⟩,
    rw [map_cons, prod_cons, ← h3, ← nat.cast_add, add_add_add_comm, ← nat.cast_add,
        ← nat.cast_add_one, add_assoc (2 * t) 1, ← bit0, ← mul_add, ← mul_add_one,
        ← mul_add_one, nat.cast_mul, nat.cast_mul, mul_div_assoc, mul_div_assoc,
        mul_assoc, mul_comm (_ / _), div_mul_div_cancel, add_right_comm],
    exact ne_of_gt (nat.cast_pos.mpr X) }
end

lemma bit1_two_pow_sub_one (k : ℕ) : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 :=
  let h := nat.one_le_pow k 2 $ nat.succ_pos 1 in
  by rw [two_mul, add_assoc, nat.sub_add_cancel h, add_comm,
    ← nat.add_sub_assoc h, ← two_mul, ← pow_succ]

/-- Final solution -/
theorem final_solution : ∀ k : ℕ, good k (2 ^ k - 1)
| 0 := good_zero_zero
| (k+1) := cast (congr_arg _ $ bit1_two_pow_sub_one k) $
    good_succ_bit1_of_good (final_solution k)

end IMO2013N2
end IMOSL
