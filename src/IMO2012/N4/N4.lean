import data.int.basic data.set.finite tactic.norm_fin

/-! # IMO 2012 N4 -/

open function
open_locale classical

namespace IMOSL
namespace IMO2012N4

def friendly (a : ℤ) := ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ (m ^ 2 + n) * (n ^ 2 + m) = a * (m - n) ^ 3



private lemma friendly_1mod4 (k : ℤ) (h : 0 < k) : friendly (4 * k + 1) :=
begin
  use [2 * k + 1, k],
  rw and_iff_right h; split,
  exact add_pos (mul_pos two_pos h) one_pos,
  rw [add_sq, mul_pow, mul_one, ← mul_assoc, sq, ← mul_add, one_pow, add_assoc, sq, ← mul_add_one,
      add_comm (1 : ℤ), ← mul_assoc, ← add_one_mul, mul_two, ← bit0, two_mul, add_assoc,
      ← add_assoc, ← mul_add_one, ← add_one_mul, add_sub_cancel', ← sq, mul_assoc, ← pow_succ]
end

theorem final_solution_part1 : 500 ≤ fintype.card {a : fin 2012 // friendly (a + 1)} :=
begin
  let f : fin 500 → {a : fin 2012 // friendly (a + 1)} := λ (n : fin 500),
  ⟨ { val := 4 * (n + 1),
      property := lt_trans ((mul_lt_mul_left four_pos).mpr (add_lt_add_right n.is_lt 1))
        (by norm_num) },
    by simp only [int.coe_nat_bit0, nat.cast_add, nat.cast_one, nat.cast_mul,
      fin.coe_mk, coe_coe]; exact friendly_1mod4 _ (nat.cast_add_one_pos _)⟩,
  suffices : injective f,
  { rw ← fintype.card_fin 500,
    exact fintype.card_le_of_injective f this },
  intros x y h; simp only [f, subtype.mk_eq_mk] at h,
  rwa [mul_eq_mul_left_iff, add_left_inj, ← fin.ext_iff, or_iff_left] at h,
  exact four_ne_zero
end








end IMO2012N4
end IMOSL
