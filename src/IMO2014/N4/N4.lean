import number_theory.basic

/-! # IMO 2014 N4 -/

namespace IMOSL
namespace IMO2014N4

open set function

/-- If `k` is even and `k % m = 1`, then `k / m` is odd. -/
private lemma even_div_odd_one_mod {k m : ℕ} (h : even k) (h0 : k % m = 1) : odd (k / m) :=
  by rw [← nat.div_add_mod k m, nat.even_add, h0, iff_false_right nat.not_even_one,
    ← nat.odd_iff_not_even, nat.odd_mul] at h; exact h.2



/-- Final solution -/
theorem final_solution {n : ℕ} (h : 1 < n) : {k : ℕ | odd (n ^ k / k)}.infinite :=
begin
  suffices : ∃ f : ℕ → ℕ, injective f ∧ ∀ k : ℕ, odd (n ^ f k / f k),
    rcases this with ⟨f, h0, h1⟩; exact infinite_of_injective_forall_mem h0 h1,
  cases n.even_or_odd with h0 h0, rotate,

  ---- Case 1: `n > 1` is odd. Choose `f(k) = n^k`.
  { refine ⟨has_pow.pow n, nat.pow_right_injective h, λ k, _⟩,
    rw nat.pow_div (le_of_lt (nat.lt_pow_self h k)) (lt_trans one_pos h),
    exact h0.pow },

  rw [nat.lt_iff_add_one_le, ← bit0, le_iff_lt_or_eq] at h,
  rcases h with h | rfl,

  ---- Case 2: `n > 2` is even. Choose `f(k) = (n - 1) ^ (k + 1)`
  { -- Injectivity
    refine ⟨λ k, (n - 1) ^ k.succ, λ x y h1, _, λ k, _⟩,
    rw ← nat.succ_inj'; exact nat.pow_right_injective (nat.le_pred_of_lt h) h1,

    -- The main work
    obtain ⟨n, rfl⟩ := nat.exists_eq_succ_of_ne_zero (ne_zero_of_lt h),
    rw nat.succ_lt_succ_iff at h,
    rw [nat.succ_eq_add_one, nat.add_sub_cancel],
    refine even_div_odd_one_mod (nat.even_pow.mpr ⟨h0, pow_ne_zero _ (ne_zero_of_lt h)⟩) _,
    nth_rewrite 1 ← nat.mod_eq_of_lt (one_lt_pow h k.succ_ne_zero),
    rw [eq_comm, ← nat.modeq, nat.modeq_iff_dvd, nat.cast_one,
        int.coe_nat_pow, int.coe_nat_pow, nat.cast_add_one],
    nth_rewrite 1 ← one_pow (n ^ k.succ),
    refine dvd_trans (pow_dvd_pow _ k.succ.le_succ) (dvd_sub_pow_of_dvd_sub _ k.succ),
    rw add_sub_cancel },

  ---- Case 3: `n = 2`. Choose `f(k) = 3 ⬝ 4 ^ (k + 1)`
  { -- Injectivity
    clear h0; refine ⟨λ k, 2 ^ (2 * k.succ) * 3, λ x y h, _, λ k, _⟩,
    rw [mul_eq_mul_right_iff, or_iff_left (three_ne_zero : 3 ≠ 0)] at h,
    rw [← nat.succ_inj', ← mul_right_inj' (two_ne_zero : 2 ≠ 0)],
    exact nat.pow_right_injective (le_refl 2) h,

    -- The main work
    have h : 1 < 3 := by norm_num,
    have h0 : 2 * k.succ < 2 ^ (2 * k.succ) * 3 :=
      lt_trans (nat.lt_pow_self one_lt_two _) (lt_mul_of_one_lt_right (pow_pos two_pos _) h),
    rw lt_iff_exists_add at h0; rcases h0 with ⟨c, h1, h0⟩,
    rw [← nat.div_div_eq_div_mul, h0, nat.pow_div le_self_add two_pos, nat.add_sub_cancel_left],
    refine even_div_odd_one_mod (nat.even_pow.mpr ⟨even_two, ne_of_gt h1⟩) _,
    replace h1 : 2 ∣ 2 ^ (2 * nat.succ k) * 3 :=
      dvd_mul_of_dvd_left (dvd_pow_self 2 (mul_ne_zero two_ne_zero k.succ_ne_zero)) 3,
    rw [h0, ← nat.dvd_add_iff_right ⟨k.succ, rfl⟩] at h1,
    clear h0 k; rcases h1 with ⟨d, rfl⟩,
    rw [pow_mul, nat.pow_mod]; norm_num }
end

end IMO2014N4
end IMOSL
