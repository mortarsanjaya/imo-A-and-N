import data.pnat.basic data.int.basic algebra.group_power.basic

/-! # IMO 2013 N1 -/

namespace IMOSL
namespace IMO2013N1

/-- Final solution -/
theorem final_solution (f : ℕ+ → ℕ+) : (∀ m n : ℕ+, m ^ 2 + f n ∣ m * f m + n) ↔ f = id :=
begin
  symmetry; split,
  rintros rfl m n,
  rw [id.def, id.def, sq],
  intros h; funext n,
  rw id.def; apply le_antisymm,
  { replace h := h (f n) n,
    rw [sq, ← mul_add_one] at h,
    replace h := dvd_trans (dvd_mul_right _ _) h,
    rw [pnat.dvd_iff, pnat.add_coe, pnat.mul_coe, nat.dvd_add_right ⟨_, rfl⟩, ← pnat.dvd_iff] at h,
    exact pnat.le_of_dvd h },
  { replace h := pnat.le_of_dvd (h n n),
    have h0 : 1 ≤ n := n.one_le,
    rw [le_iff_eq_or_lt, eq_comm] at h0,
    rcases h0 with rfl | h0,
    exact (f 1).one_le,
    rw [← pnat.coe_le_coe, ← int.coe_nat_le_coe_nat_iff] at h ⊢,
    simp only [sq, pnat.add_coe, pnat.mul_coe, int.coe_nat_add, int.coe_nat_mul] at h,
    generalizes [hx : ((f n : ℕ) : ℤ) = x, hy : ((n : ℕ) : ℤ) = y],
    rw [← pnat.coe_lt_coe, ← int.coe_nat_lt_coe_nat_iff, ← hy, ← sub_pos] at h0,
    rw [← hx, ← hy, ← sub_nonneg, add_sub_add_comm, ← mul_sub,
        ← neg_sub x y, ← neg_one_mul, ← add_mul, ← sub_eq_add_neg] at h,
    rwa [← sub_nonneg, ← mul_nonneg_iff_right_nonneg_of_pos h0] }
end

end IMO2013N1
end IMOSL
