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
    (mul_le_mul_iff_left k).mp $ (add_le_add_iff_right n).mp $
    (add_one_mul k n).symm.trans_le $ (add_le_add_iff_right (f n)).mp $
    add_right_comm (k * f n) (f n) n ▸ (add_one_mul k (f n)) ▸ h0 ▸ pnat.le_of_dvd (h n n)),
λ h m n, h.symm ▸ dvd_refl _⟩

end IMO2013N1
end IMOSL
