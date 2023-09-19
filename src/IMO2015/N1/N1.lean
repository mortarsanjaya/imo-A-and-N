import data.int.parity

/-! # IMO 2015 N1 -/

namespace IMOSL
namespace IMO2015N1

def f (n : ℤ) := n * (n / 2)

lemma main_claim {c m : ℤ} (h : 2 * c ∣ m - 3) (h0 : 2 * c ∣ f m - 3) :
  2 * (2 * c) ∣ m - 3 :=
(eq_or_ne c 0).elim
---- Case 1: `c = 0`
(λ h1, suffices 2 * c = 2 * (2 * c), from this ▸ h, h1.symm ▸ rfl)
---- Case 2: `c ≠ 0`
(λ h1, exists.elim h $ λ d h, suffices 2 ∣ d,
  from h.symm ▸ d.mul_comm (2 * c) ▸ mul_dvd_mul_right this _,
begin
  have X : (2 : ℤ) ≠ 0 := (int.bit0_pos int.one_pos).ne.symm,
  rw [f, eq_add_of_sub_eq h, add_mul, add_sub_assoc, mul_assoc, dvd_add_right ⟨_, rfl⟩,
      mul_assoc, add_comm, int.add_mul_div_left _ _ X, mul_add, add_comm] at h0,
  have X0 : (3 : ℤ) / 2 = 1 := rfl,
  rwa [X0, mul_one, add_sub_cancel, mul_comm, mul_left_comm,
       mul_dvd_mul_iff_left h1, bit1, add_one_mul, dvd_add_right ⟨_, rfl⟩] at h0
end)

/-- Final solution -/
theorem final_solution {M : ℤ} :
  (∃ k : ℕ, 2 ∣ (f^[k] M)) ↔ M ≠ 3 :=
iff.symm $ not_iff_comm.mp $ not_exists.trans $
---- If `f^k(M)` is odd for all `k ≥ 0`, then `M = 3`
⟨λ h, suffices ∀ x k : ℕ, 2 ^ (x + 1) ∣ (f^[k]) M - 3,
  from let K := (M - 3).nat_abs,
    h0 := int.coe_nat_lt.mpr (K.lt_succ_self.trans K.succ.lt_two_pow) in
  eq_of_sub_eq_zero $ int.eq_zero_of_abs_lt_dvd (this K 0) $
    (M - 3).coe_nat_abs.symm.trans_lt $ h0.trans_eq (int.coe_nat_pow 2 K.succ),
λ x, nat.rec_on x
  (λ x, (int.dvd_iff_mod_eq_zero _ _).mpr $ int.even_iff.mp $ int.even_sub'.mpr $
    iff_of_true (int.odd_iff.mpr $ int.two_dvd_ne_zero.mp $ h x) (odd_bit1 1))
  (λ x h0 k, main_claim (h0 k) (f.iterate_succ_apply' k M ▸ h0 (k + 1))),
---- `f^k(3)` is odd for all `k ≥ 0`
λ h x, h.symm ▸ (function.iterate_fixed (rfl : f 3 = 3) x).symm ▸
  int.two_not_dvd_two_mul_add_one 1⟩

end IMO2015N1
end IMOSL
