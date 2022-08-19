import data.int.gcd data.set.finite

/-! # IMO 2012 N4 -/

namespace IMOSL
namespace IMO2012N4

open function
open_locale classical

def friendly (a : ℤ) := ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ (m ^ 2 + n) * (n ^ 2 + m) = a * (m - n) ^ 3



private lemma friendly_1mod4 {k : ℤ} (h : 0 < k) : friendly (4 * k + 1) :=
  ⟨2 * k + 1, k, add_pos (mul_pos two_pos h) one_pos, h, by ring⟩



/- Final solution for part 1 -/
theorem final_solution_part1 (n : ℕ) :
  n ≤ fintype.card {a : fin (4 * n + 1) // friendly (a + 1)} :=
begin
  let f : fin n → {a : fin (4 * n + 1) // friendly (a + 1)} :=
    λ (j : fin n), ⟨⟨4 * (j + 1), _⟩, _⟩,
  rotate,
  { rw [nat.lt_succ_iff, mul_le_mul_left, nat.succ_le_iff],
    exacts [j.is_lt, zero_lt_four] },
  { simp; apply friendly_1mod4,
    rw [← nat.cast_one, ← nat.cast_add, nat.cast_pos]; exact (j : ℕ).succ_pos },
  suffices : injective f,
    convert fintype.card_le_of_injective f this; rw fintype.card_fin n,
  intros x y h; simp only [f, subtype.mk_eq_mk] at h,
  rwa [mul_eq_mul_left_iff, add_left_inj, ← fin.ext_iff, or_iff_left] at h,
  exact four_ne_zero
end

/- Final solution for part 2 -/
theorem final_solution_part2 : ¬friendly 2 :=
begin
  rintros ⟨m, n, hm, hn, h⟩,
  have h0 : 0 < m - n :=
  begin
    rw lt_iff_not_le; intros h0,
    replace h := le_of_eq_of_le h
      (mul_nonpos_of_nonneg_of_nonpos zero_le_two (by rwa pow_bit1_nonpos_iff)),
    rw ← not_lt at h,
    exact h (mul_pos (add_pos (pow_pos hm 2) hn) (add_pos (pow_pos hn 2) hm))
  end,

  have h1 : ∃ s : ℤ, 0 < s ∧ (m + n - 1 + s) ^ 2 = (m + n - 1) ^ 2 + 8 * (m - n) :=
  begin
    replace h : (m ^ 2 + n + n ^ 2 + m) ^ 2 = (m - n) ^ 2 * ((m + n - 1) ^ 2 + 8 * (m - n)) :=
      by convert (congr_arg (λ x, 4 * x + (m ^ 2 + n - n ^ 2 - m) ^ 2) h); ring,
    have h1 : (m - n) ^ 2 ∣ (m ^ 2 + n + n ^ 2 + m) ^ 2 := ⟨_, h⟩,
    rw int.pow_dvd_pow_iff two_pos at h1,
    cases h1 with t h1,
    rw [h1, mul_pow, mul_right_inj' (ne_of_gt (pow_pos h0 2))] at h,
    use t - (m + n - 1),
    rw [← h, add_sub_cancel'_right, and_iff_left rfl, sub_pos],
    refine lt_of_pow_lt_pow 2 _ _,
    { rw [← mul_nonneg_iff_right_nonneg_of_pos h0, ← h1, add_assoc],
      apply add_nonneg; refine add_nonneg (sq_nonneg _) (le_of_lt _),
      exacts [hn, hm] },
    { rw [h, lt_add_iff_pos_right],
      exact mul_pos (by norm_num) h0 }
  end,
  
  rcases h1 with ⟨s, h1, h2⟩,
  rw [← sub_eq_iff_eq_add', sq_sub_sq, add_sub_cancel', add_right_comm, ← two_mul] at h2,
  obtain ⟨t, rfl⟩ : 2 ∣ s :=
  begin
    replace h2 : 2 ∣ (2 * (m + n - 1) + s) * s :=
      ⟨4 * (m - n), by rw [h2, ← mul_assoc, two_mul, ← bit0]⟩,
    rw [add_mul, mul_assoc, dvd_add_right ⟨_, rfl⟩, ← sq] at h2,
    exact prime.dvd_of_dvd_pow int.prime_two h2
  end,

  rw [← mul_zero (2 : ℤ), mul_lt_mul_left (two_pos : 0 < (2 : ℤ)), int.lt_iff_add_one_le,
      zero_add, le_iff_eq_or_lt, eq_comm, int.lt_iff_add_one_le, ← bit0] at h1,
  change (8 : ℤ) with (2 + 2) + (2 + 2) at h2,
  rw [← mul_add, mul_mul_mul_comm, ← two_mul, mul_comm (2 : ℤ) (2 + 2), mul_assoc (2 + 2 : ℤ),
      ← two_mul, ← sq, mul_right_inj' (pow_ne_zero 2 (two_ne_zero : (2 : ℤ) ≠ 0)), mul_comm] at h2,
  rcases h1 with rfl | h1,
  { rw [one_mul, sub_add_cancel, mul_sub, eq_sub_iff_add_eq,
        add_assoc, ← one_add_mul, two_mul, add_right_inj] at h2,
    rw [← h2, ← sub_eq_zero] at h; ring_nf at h,
    revert h; refine ne_of_gt (mul_pos (add_pos _ three_pos) (pow_pos hn 2)),
    exact mul_pos (add_pos (mul_pos (by norm_num) hn) (by norm_num)) hn },
  { revert h2; refine ne_of_gt (lt_of_le_of_lt ((mul_le_mul_right h0).mpr h1) _),
    rw mul_lt_mul_left (lt_of_lt_of_le two_pos h1),
    refine lt_of_lt_of_le _ (add_le_add_left h1 _),
    rw [bit0, sub_add_add_cancel, int.lt_add_one_iff, sub_le_iff_le_add,
        add_assoc, le_add_iff_nonneg_right, ← two_mul],
    exact mul_nonneg zero_le_two (le_of_lt hn) },
end

end IMO2012N4
end IMOSL
