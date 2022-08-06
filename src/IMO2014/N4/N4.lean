import data.nat.parity number_theory.basic data.fintype.basic data.set.finite

/-! # IMO 2014 N4 -/

namespace IMOSL
namespace IMO2014N4



private theorem case_odd {n : ℕ} (h : 1 < n) (h0 : odd n) (m : ℕ) : odd (n ^ (n ^ m) / (n ^ m)) :=
  by rw nat.pow_div (le_of_lt (nat.lt_pow_self h m)) (lt_trans one_pos h); exact h0.pow

private theorem case_even_ne_two {n : ℕ} (h : 2 < n) (h0 : even n) {i : ℕ} (h1 : 0 < i) :
  odd (n ^ ((n - 1) ^ i) / (n - 1) ^ i) :=
begin
  cases n with _ n,
  exfalso; exact lt_asymm h two_pos,
  rw [nat.even_add_one, ← nat.odd_iff_not_even] at h0,
  rw nat.succ_lt_succ_iff at h,
  rw [nat.succ_eq_add_one, nat.add_sub_cancel],
  have h2 : n ^ i ≠ 0 := pow_ne_zero i (ne_of_gt (lt_trans one_pos h)),
  suffices : n ^ (i + 1) ∣ (n + 1) ^ n ^ i - 1,
  { replace this := dvd_trans (dvd_mul_left (n ^ i) n) this,
    cases this with c this,
    rw nat.sub_eq_iff_eq_add (le_of_lt (one_lt_pow (lt_trans h (lt_add_one n)) h2)) at this,
    rw [this, add_comm, nat.add_mul_div_left 1 c (pow_pos (lt_trans one_pos h) i),
        nat.div_eq_zero (one_lt_pow h (ne_of_gt h1)), zero_add, nat.odd_iff_not_even],
    intros h3,
    replace h3 : ¬even (n ^ i * c + 1) :=
      by rw [nat.even_add_one, not_not]; exact h3.mul_left (n ^ i),
    rw [← this, nat.even_pow, and_iff_left h2, nat.even_add_one, ← nat.odd_iff_not_even] at h3,
    exact h3 h0 },
  replace h1 : (n : ℤ) ∣ n + 1 - 1 := by rw add_sub_cancel,
  replace h1 := dvd_sub_pow_of_dvd_sub h1 i,
  rwa [one_pow, ← int.coe_nat_pow, ← (nat.cast_one : (1 : ℤ) = 1), ← nat.cast_add,
       ← int.coe_nat_pow, ← nat.cast_sub, int.coe_nat_dvd] at h1,
  exact le_of_lt (one_lt_pow (lt_trans h (lt_add_one n)) h2)
end

private theorem case_two {i : ℕ} (h : 0 < i) : odd (2 ^ (3 * 4 ^ i) / (3 * 4 ^ i)) :=
begin
  sorry
end



/-- Final solution -/
theorem final_solution {n : ℕ} (h : 1 < n) : {k : ℕ | odd (n ^ k / k)}.infinite :=
begin
  suffices : ∃ f : ℕ → ℕ, function.injective f ∧ set.range f ⊆ {k : ℕ | odd (n ^ k / k)},
  { rcases this with ⟨f, h0, h1⟩,
    exact set.infinite.mono h1 (set.infinite_range_of_injective h0) },
  cases n.even_or_odd with h0 h0,
  rw [nat.lt_iff_add_one_le, ← bit0, le_iff_eq_or_lt, eq_comm] at h,
  rcases h with rfl | h,
  { use (λ i, 3 * 4 ^ i.succ); split,
    intros x y h; simp only [] at h,
    rw [pow_succ, pow_succ, ← mul_assoc, ← mul_assoc, mul_right_inj'] at h,
    exact nat.pow_right_injective (by norm_num) h,
    norm_num,
    rintros k ⟨i, rfl⟩,
    exact case_two i.succ_pos },
  { use (λ i, (n - 1) ^ i.succ); split,
    intros x y h1; simp only [] at h1,
    rw ← nat.succ_inj'; refine nat.pow_right_injective (nat.le_pred_of_lt h) h1,
    rintros k ⟨i, rfl⟩,
    exact case_even_ne_two h h0 i.succ_pos },
  { use (has_pow.pow n); split,
    exact nat.pow_right_injective h,
    rintros k ⟨i, rfl⟩; exact case_odd h h0 i },
end

end IMO2014N4
end IMOSL
