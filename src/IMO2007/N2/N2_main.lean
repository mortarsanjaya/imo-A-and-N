import ring_theory.int.basic data.nat.parity

/-! # IMO 2007 N2 -/

namespace IMOSL
namespace IMO2007N2

set_option profiler true
set_option profiler.threshold 0.05

/-- Final solution with explicit `k` -/
theorem final_solution' {b n : ℕ} (h : 0 < b) (h0 : ∃ c : ℤ, (b ^ 2 : ℤ) ∣ b - c ^ n) :
  ∃ a : ℤ, (b : ℤ) = a ^ n :=
---- Reduce to `c^n ∼ b`
suffices ∃ c : ℤ, associated (c ^ n) b,
  from exists.elim this $ λ c h1, (int.associated_iff.mp h1).elim (λ h1, ⟨c, h1.symm⟩) $
    λ h1, ⟨-c, suffices odd n, from (neg_eq_iff_eq_neg.mpr h1).symm.trans (this.neg_pow c).symm,
      nat.odd_iff_not_even.mpr $ λ h0, (h0.pow_nonneg c).not_lt $
        h1.trans_lt $ neg_neg_of_pos $ int.coe_nat_pos.mpr h⟩,
---- Prove `c^n ∼ b`
exists.elim h0 $ λ c h0, exists.elim h0 $ λ d h0,
have h0 : (b : ℤ) * (1 - b * d) = c ^ n,
  from (mul_one_sub _ _).trans $ mul_assoc (b : ℤ) b d ▸ sq (b : ℤ) ▸
    sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add'.mp h0),
have h1 : gcd (b : ℤ) (1 - b * d) = 1,
  from (gcd_eq_of_dvd_sub_right ⟨d, sub_sub_cancel 1 (b * d)⟩).symm.trans (gcd_one_right b),
exists_associated_pow_of_mul_eq_pow (int.is_unit_iff.mpr $ or.inl h1) h0



/-- Final solution -/
theorem final_solution {b n : ℕ} (h : 0 < b)
    (h0 : ∀ k : ℕ, 0 < k → ∃ c : ℤ, (k : ℤ) ∣ b - c ^ n) :
  ∃ a : ℤ, (b : ℤ) = a ^ n :=
  final_solution' h $ int.coe_nat_pow b 2 ▸ h0 (b ^ 2) (pow_pos h 2)

end IMO2007N2
end IMOSL
