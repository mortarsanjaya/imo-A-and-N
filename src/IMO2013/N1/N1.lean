import data.pnat.basic

/-! # IMO 2013 N1 -/

namespace IMOSL
namespace IMO2013N1

/-- Final solution -/
theorem final_solution (f : ℕ+ → ℕ+) :
  (∀ m n : ℕ+, m * m + f n ∣ m * f m + n) ↔ f = id :=
begin
  symmetry; refine ⟨λ h m n, _, λ h, funext (λ n, le_antisymm _ _)⟩,
  rw h; exact dvd_refl _,

  ---- `f(n) ≤ n`
  { replace h := h (f n) n,
    rw ← mul_add_one at h,
    replace h := dvd_trans (dvd_mul_right _ _) h,
    rw [pnat.dvd_iff, pnat.add_coe, pnat.mul_coe, nat.dvd_add_right ⟨_, rfl⟩, ← pnat.dvd_iff] at h,
    exact pnat.le_of_dvd h },

  ---- `f(n) ≥ n`
  { rcases eq_or_ne n 1 with h | h0,
    exact le_of_eq_of_le h (f n).one_le,
    replace h := pnat.le_of_dvd (h n n),
    generalize_hyp : f n = m at h ⊢; clear f,
    replace h0 := pnat.exists_eq_succ_of_ne_one h0,
    rcases h0 with ⟨k, rfl⟩,
    rwa [add_one_mul, add_right_comm, add_le_add_iff_right,
         add_one_mul, add_le_add_iff_right, mul_le_mul_iff_left] at h }
end

end IMO2013N1
end IMOSL
