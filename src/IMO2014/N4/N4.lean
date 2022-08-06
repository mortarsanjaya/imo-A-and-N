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
  have h3 := le_of_lt (one_lt_pow (lt_trans h (lt_add_one n)) h2),
  suffices : n ^ (i + 1) ∣ (n + 1) ^ n ^ i - 1,
  { replace this := dvd_trans (dvd_mul_left (n ^ i) n) this,
    cases this with c this,
    rw nat.sub_eq_iff_eq_add h3 at this,
    rw [this, add_comm, nat.add_mul_div_left 1 c (pow_pos (lt_trans one_pos h) i),
        nat.div_eq_zero (one_lt_pow h (ne_of_gt h1)), zero_add, nat.odd_iff_not_even],
    intros h4,
    replace h4 : ¬even (n ^ i * c + 1) :=
      by rw [nat.even_add_one, not_not]; exact h4.mul_left (n ^ i),
    rw [← this, nat.even_pow, and_iff_left h2, nat.even_add_one, ← nat.odd_iff_not_even] at h4,
    exact h4 h0 },
  replace h1 : (n : ℤ) ∣ n + 1 - 1 := by rw add_sub_cancel,
  replace h1 := dvd_sub_pow_of_dvd_sub h1 i,
  rwa [one_pow, ← int.coe_nat_pow, ← (nat.cast_one : (1 : ℤ) = 1), ← nat.cast_add,
       ← int.coe_nat_pow, ← nat.cast_sub h3, int.coe_nat_dvd] at h1
end

private theorem case_two {i : ℕ} (h : 0 < i) : odd (2 ^ (3 * 2 ^ (2 * i)) / (3 * 2 ^ (2 * i))) :=
begin
  have h0 : 2 * i < 2 ^ (2 * i) * 3 := lt_trans (nat.lt_pow_self one_lt_two (2 * i))
    (lt_mul_of_one_lt_right (pow_pos two_pos _) (by norm_num)),
  suffices : 3 ∣ 2 ^ (2 ^ (2 * i) * 3 - 2 * i) - 1,
  { rw [mul_comm, ← nat.div_div_eq_div_mul, nat.pow_div (le_of_lt h0) two_pos],
    cases this with c h1,
    rw nat.sub_eq_iff_eq_add (nat.one_le_pow _ _ two_pos) at h1,
    rw [h1, add_comm, nat.add_mul_div_left 1 c three_pos,
        nat.div_eq_zero (by norm_num : 1 < 3), zero_add, nat.odd_iff_not_even],
    intros h2,
    replace h2 : ¬even (3 * c + 1) := by rw [nat.even_add_one, not_not]; exact h2.mul_left 3,
    rw ← tsub_pos_iff_lt at h0,
    rw [← h1, nat.even_pow, and_iff_left (ne_of_gt h0)] at h2,
    exact h2 even_two },
  generalize h1 : 2 ^ (2 * i) * 3 - 2 * i = k,
  replace h1 : 2 ∣ k :=
  begin
    rw [← h1, nat.dvd_add_iff_left ⟨i, rfl⟩, nat.sub_add_cancel (le_of_lt h0)],
    use 2 ^ (2 * i - 1) * 3,
    rw [← mul_assoc, ← pow_succ, nat.sub_add_cancel (mul_pos two_pos h)]
  end,
  rcases h1 with ⟨m, rfl⟩,
  clear h h0; induction m with m m_ih,
  rw [mul_zero, pow_zero, nat.sub_self],
  exact dvd_zero 3,
  cases m_ih with c h,
  rw nat.sub_eq_iff_eq_add (nat.one_le_pow _ _ two_pos) at h,
  rw [mul_add_one, pow_add, h, add_one_mul]; norm_num,
  use c * 4; rw mul_assoc
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
  { use (λ i, 3 * 2 ^ (2 * i.succ)); split,
    intros x y h; simp only [] at h,
    rw mul_right_inj' (by norm_num : 3 ≠ 0) at h,
    replace h := nat.pow_right_injective (le_refl 2) h,
    rwa [mul_right_inj' (two_ne_zero : (2 : ℕ) ≠ 0), nat.succ_inj'] at h,
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
