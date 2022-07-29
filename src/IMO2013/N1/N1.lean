import data.pnat.basic data.nat.basic algebra.group_power.basic

/-! # IMO 2013 N1 -/

namespace IMOSL
namespace IMO2013N1

/-- Final solution -/
theorem final_solution (f : ℕ+ → ℕ+) :
  (∀ m n : ℕ+, m ^ 2 + f n ∣ m * f m + n) ↔ f = id :=
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
    rw [← pnat.coe_le_coe, ← not_lt] at h ⊢,
    intros h0; apply h; clear h,
    rw [sq, pnat.add_coe, pnat.add_coe, pnat.mul_coe, pnat.mul_coe],
    set x := (n : ℕ); clear_value x,
    have h := lt_of_le_of_lt (nat.succ_le_iff.mpr (f n).pos) h0,
    have h1 := le_of_lt h,
    set y := (f n : ℕ); clear_value y,
    rw [← nat.sub_add_cancel h1, add_one_mul, add_one_mul, nat.sub_add_cancel h1,
        add_right_comm, add_lt_add_iff_right, add_lt_add_iff_right],
    exact (mul_lt_mul_left (nat.sub_pos_of_lt h)).mpr h0 }
end

end IMO2013N1
end IMOSL
