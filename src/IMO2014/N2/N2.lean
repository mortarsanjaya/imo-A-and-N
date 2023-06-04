import data.int.parity tactic.ring

/-! # IMO 2014 N2 -/

namespace IMOSL
namespace IMO2014N2

def good (x y : ℤ) := 7 * (x ^ 2 + y ^ 2) - 13 * (x * y) = (|x - y| + 1) ^ 3





def A (m : ℤ) := m ^ 3 + 2 * m ^ 2 - m - 1
def B (m : ℤ) := m ^ 3 + m ^ 2 - 2 * m - 1

lemma mul2_add1_sq (m : ℤ) : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 :=
  by ring

lemma A_sub_B (m : ℤ) : A m - B m = (m + 1) * m :=
  by rw [A, B]; ring

lemma good_A_B (m : ℤ) : good (A m) (B m) :=
  suffices 0 ≤ (m + 1) * m,
    by rw [good, A_sub_B, abs_eq_self.mpr this, A, B]; ring,
  (le_or_lt 0 m).elim (λ h, mul_nonneg (add_nonneg h zero_le_one) h)
    (λ h, mul_nonneg_of_nonpos_of_nonpos (int.add_one_le_iff.mpr h) (le_of_lt h))

lemma good_swap {x y : ℤ} (h : good x y) : good y x :=
  (congr_arg2 (λ u v : ℤ, 7 * u - 13 * v) (add_comm _ _) (mul_comm y x)).trans $
    h.trans $ congr_arg (λ u : ℤ, (u + 1) ^ 3) (abs_sub_comm x y)

lemma good_le_imp {x y : ℤ} (h : good x y) (h0 : y ≤ x) : ∃ m : ℤ, x = A m ∧ y = B m :=
begin
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = n + y := ⟨x - y, by rw sub_add_cancel⟩,
  rw le_add_iff_nonneg_left at h0,
  rw [good, add_sub_cancel, abs_eq_self.mpr h0, ← add_left_inj (-7 * n ^ 2)] at h; ring_nf at h,
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
    use 1; unfold A B; norm_num },
  { obtain ⟨m, rfl⟩ : ∃ m : ℤ, c = 2 * m + 1 :=
    begin
      use c / 2; convert (int.div_add_mod c 2).symm,
      rw [eq_comm, ← int.not_even_iff, ← int.even_pow' two_ne_zero, h, ← int.odd_iff_not_even],
      use 2 * n; rw [← mul_assoc, two_mul, ← bit0]
    end,
    rw [mul2_add1_sq, add_left_inj, mul_eq_mul_left_iff, or_comm] at h,
    rcases h with h | rfl,
    exfalso; exact four_ne_zero h,
    rw [← eq_sub_iff_add_eq, mul_add_one, add_sub_assoc, sub_sub_cancel_left,
        ← sub_eq_add_neg, mul_left_comm, ← mul_sub_one, mul_eq_mul_left_iff, or_comm] at h1,
    cases h1 with h1,
    exfalso; exact two_ne_zero h1,
    use m; rw [A, B, h1],
    split; ring }
end

/-- Final solution -/
theorem final_solution (x y : ℤ) :
  good x y ↔ ((∃ m : ℤ, x = A m ∧ y = B m) ∨ (∃ m : ℤ, y = A m ∧ x = B m)) :=
begin
  split,
  { intros h,
    cases le_total y x with h0 h0,
    left; exact good_le_imp h h0,
    right; exact good_le_imp (good_swap h) h0 },
  { rintros (⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩),
    exact good_A_B m,
    exact good_swap (good_A_B m) }
end

end IMO2014N2
end IMOSL
