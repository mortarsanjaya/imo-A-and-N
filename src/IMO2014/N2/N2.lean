import data.int.gcd data.int.parity tactic.ring

/-! # IMO 2014 N2, Integer Version -/

namespace IMOSL
namespace IMO2014N2

def good (x y : ℤ) := 7 * x ^ 2 - 13 * (x * y) + 7 * y ^ 2 = (|x - y| + 1) ^ 3

def good_pair (m : ℤ) : ℤ × ℤ := (m ^ 3 + 2 * m ^ 2 - m - 1, m ^ 3 + m ^ 2 - 2 * m - 1)



section extra

private lemma mul2_add1_sq (m : ℤ) : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 :=
  by rw [add_sq, mul_one, one_pow, mul_pow, ← mul_assoc, sq, ← mul_add, two_mul, ← bit0]

end extra



private lemma good_swap {x y : ℤ} (h : good x y) : good y x :=
  by unfold good at h ⊢; rw [abs_sub_comm, ← h, sub_add_comm, mul_comm x y]

private lemma good_y_le_x {x y : ℤ} (h : good x y) (h0 : y ≤ x) : ∃ m : ℤ, (x, y) = good_pair m :=
begin
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = n + y := ⟨x - y, by rw sub_add_cancel⟩,
  rw le_add_iff_nonneg_left at h0,
  dsimp only [good] at h,
  rw [add_sub_cancel, abs_eq_self.mpr h0, ← add_left_inj (-7 * n ^ 2)] at h; ring_nf at h,
  replace h : (2 * y + n) ^ 2 = (n - 2) ^ 2 * (4 * n + 1) :=
    by convert (congr_arg (λ c, 4 * c + n ^ 2) h); ring,
  obtain ⟨c, h1⟩ : n - 2 ∣ 2 * y + n :=
    by rw ← int.pow_dvd_pow_iff two_pos; exact ⟨4 * n + 1, h⟩,
  rw [h1, mul_pow, mul_eq_mul_left_iff, or_comm] at h,
  cases h with h h,
  { replace h := pow_eq_zero h,
    rw sub_eq_zero at h; subst h,
    rw [sub_self, zero_mul, ← mul_add_one, mul_eq_zero] at h1,
    cases h1 with h1,
    exfalso; exact two_ne_zero h1,
    rw add_eq_zero_iff_eq_neg at h1; subst h1,
    use 1; unfold good_pair; norm_num },
  { obtain ⟨m, rfl⟩ : ∃ m : ℤ, c = 2 * m + 1 :=
    begin
      use c / 2; convert (int.div_add_mod c 2).symm,
      rw [eq_comm, ← int.not_even_iff, ← int.even_pow' two_ne_zero, h, ← int.odd_iff_not_even],
      use 2 * n; rw [← mul_assoc, two_mul, ← bit0]
    end,
    rw [mul2_add1_sq, add_left_inj, mul_eq_mul_left_iff, or_comm] at h,
    cases h with h h,
    exfalso; exact four_ne_zero h,
    subst h; use m,
    rw [← eq_sub_iff_add_eq, mul_add_one, add_sub_assoc, sub_sub_cancel_left,
        ← sub_eq_add_neg, mul_left_comm, ← mul_sub_one, mul_eq_mul_left_iff, or_comm] at h1,
    cases h1 with h1,
    exfalso; exact two_ne_zero h1,
    unfold good_pair,
    rw [h1, prod.mk.inj_iff],
    split; ring }
end

private lemma good_pair_is_good (m : ℤ) : good (good_pair m).1 (good_pair m).2 :=
begin
  suffices : 0 ≤ (m + 1) * m,
  { unfold good good_pair; ring_nf,
    rw abs_eq_self.mpr this; ring },
  have h0 := sq_nonneg (2 * m + 1),
  rw [mul2_add1_sq, le_iff_lt_or_eq, ← int.add_one_le_iff, add_le_add_iff_right] at h0,
  cases h0 with h0 h0,
  { rw [add_one_mul, ← sq],
    rwa zero_le_mul_left (four_pos : 0 < (4 : ℤ)) at h0 },
  { rw [eq_comm, add_eq_zero_iff_eq_neg] at h0,
    replace h0 : 4 ∣ (-1 : ℤ) := ⟨m ^ 2 + m, h0.symm⟩,
    rw dvd_neg at h0,
    replace h0 := int.eq_one_of_dvd_one zero_le_four h0,
    exfalso; revert h0; norm_num }
end



/-- Final solution -/
theorem final_solution (x y : ℤ) :
  good x y ↔ (∃ m : ℤ, (x, y) = good_pair m) ∨ (∃ m : ℤ, (y, x) = good_pair m) :=
begin
  split,
  { intros h,
    cases le_total y x with h0 h0,
    left; exact good_y_le_x h h0,
    right; exact good_y_le_x (good_swap h) h0 },
  { rintros (⟨m, h⟩ | ⟨m, h⟩),
    all_goals {
      have h0 := good_pair_is_good m,
      rwa ← h at h0 },
    exact good_swap h0 }
end

end IMO2014N2
end IMOSL
