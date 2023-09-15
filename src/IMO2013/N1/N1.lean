import data.pnat.basic

/-! # IMO 2013 N1 -/

namespace IMOSL
namespace IMO2013N1

/-- Final solution -/
theorem final_solution (f : ℕ+ → ℕ+) :
  (∀ m n : ℕ+, m * m + f n ∣ m * f m + n) ↔ f = id :=
⟨λ h, funext $ λ n, le_antisymm
  ---- `f(n) ≤ n`
  (pnat.le_of_dvd $ pnat.dvd_iff.mpr $ (nat.dvd_add_right ⟨(f (f n)), rfl⟩).mp $
    pnat.dvd_iff.mp $ dvd_trans ⟨f n + 1, (mul_add_one (f n) (f n)).symm⟩ (h (f n) n))
  ---- `f(n) ≥ n`
  ((eq_or_ne n 1).elim (λ h, h.trans_le (f n).one_le) $
    λ h0, exists.elim (pnat.exists_eq_succ_of_ne_one h0) $ λ k h0,
    let h := pnat.le_of_dvd (h (k + 1) (k + 1)) in
      by rwa [add_one_mul, add_right_comm, add_le_add_iff_right,
        add_one_mul, add_le_add_iff_right, mul_le_mul_iff_left, ← h0] at h),
λ h m n, h.symm ▸ dvd_refl _⟩

end IMO2013N1
end IMOSL
