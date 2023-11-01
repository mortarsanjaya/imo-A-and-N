import data.int.div data.nat.prime

/-! # IMO 2009 N3 -/

namespace IMOSL
namespace IMO2009N3

/-- Final solution -/
theorem final_solution {f : ℕ → ℤ} (h : ∀ a b : ℕ, (a : ℤ) - b ∣ f a - f b)
  {K : ℕ} (h0 : ∀ p : ℕ, p.prime → K < p → ∀ c, ¬(p : ℤ) ∣ f c) :
  ∃ C : ℤ, f = λ _, C :=
suffices ∀ b, f b = f 0, from ⟨f 0, funext this⟩,
---- Reduce to showing that there exists `N > 0` such that `f(kN) = f(0)` for all `k`
suffices ∃ N : ℕ, 0 < N ∧ ∀ k, f (k * N) = f 0, from exists.elim this $ λ N h1 b,
  suffices ∃ k : ℕ, (f b - f (k * N)).nat_abs < ((b : ℤ) - ((k * N : ℕ) : ℤ)).nat_abs,
    from exists.elim this $ λ k h2, eq_of_sub_eq_zero $ h1.2 k ▸
      int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs (h _ _) h2,
  exists.elim (exists_gt (b + (f b - f 0).nat_abs)) $ λ k h2,
    ⟨k, exists.elim (exists_pos_add_of_lt $ h2.trans_le $ nat.le_mul_of_pos_right h1.1) $
      λ d h2, exists.elim h2 $ λ h3 h2, (h1.2 k).symm ▸ h2 ▸ (lt_add_of_pos_right _ h3).trans_eq
      (by rw [add_assoc, int.coe_nat_add, sub_add_cancel', int.nat_abs_neg, int.nat_abs_of_nat])⟩,
---- Now prove that such `N` exists
have h1 : f 0 ≠ 0, from λ h1,
  exists.elim (K + 1).exists_infinite_primes $ λ p h2, h0 p h2.2 h2.1 0 ⟨0, h1⟩,
⟨4 * K.factorial * (f 0).nat_abs,
nat.mul_pos (nat.mul_pos (nat.succ_pos 3) K.factorial_pos) (int.nat_abs_pos_of_ne_zero h1),
λ k, begin
  have h2 := h (k * (4 * K.factorial * (f 0).nat_abs)) 0,
  rw [int.coe_nat_zero, sub_zero, int.coe_nat_mul, int.coe_nat_mul, int.coe_nat_abs] at h2,
  replace h2 := (mul_dvd_mul_left _ $ self_dvd_abs (f 0)).trans (dvd_of_mul_left_dvd h2),
  cases dvd_sub_self_right.mp (dvd_of_mul_left_dvd h2) with m h3,
  rw [h3, ← sub_eq_zero, ← mul_sub_one, mul_eq_zero, or_iff_right h1, sub_eq_zero],
  rw [h3, ← mul_sub_one, mul_comm, mul_dvd_mul_iff_left h1, int.coe_nat_mul] at h2,
  by_cases h4 : m.nat_abs = 1,

  -- Case 1: `|m| = 1`
  { refine (int.nat_abs_eq_iff.mp h4).resolve_right (λ h4, (nat.le_succ 2).not_lt _),
    rw [h4, ← neg_add', dvd_neg, ← int.coe_nat_succ] at h2,
    exact nat.le_of_dvd (nat.succ_pos 1) (int.coe_nat_dvd.mp $ dvd_of_mul_right_dvd h2) },

  -- Case 2: `|m| ≠ 1`
  { rcases nat.exists_prime_and_dvd h4 with ⟨p, h5, h6⟩,
    rw ← int.coe_nat_dvd_left at h6,
    have h7 : p ≤ K := le_of_not_lt
      (λ h7, (h0 p h5 h7 $ k * (4 * K.factorial * (f 0).nat_abs)).elim $
        h3.symm ▸ dvd_mul_of_dvd_right h6 (f 0)), 

    replace h2 := (int.coe_nat_dvd.mpr $ nat.dvd_factorial h5.pos h7).trans
      (dvd_of_mul_left_dvd h2),
    rw [dvd_sub_right h6, int.coe_nat_dvd_left] at h2,
    exact absurd h2 h5.not_dvd_one } 
end⟩

end IMO2009N3
end IMOSL
