import data.int.parity data.int.modeq ring_theory.coprime.lemmas

/-! # IMO 2015 N1 -/

namespace IMOSL
namespace IMO2015N1

open function

def f (n : ℤ) := n * (n / 2)

/-- Final solution -/
theorem final_solution (n : ℤ) : (∃ k : ℕ, even (f^[k] n)) ↔ n ≠ 3 :=
begin
  ---- Go for the contrapositive and prove the easy direction
  rw [← not_iff_not, not_not, not_exists, iff.comm]; split,
  rintros rfl,
  suffices : ∀ x : ℕ, f^[x] 3 = 3,
    intros x; rw this; norm_num,
  intros x; induction x with x x_ih,
  rw [iterate_zero, id.def],
  rw [iterate_succ', comp_app, x_ih]; refl,

  ---- Reduce to a more general result
  revert n; suffices : ∀ {n c : ℤ},
    c ≠ 0 → n ≡ 3 [ZMOD 2 * c] → f n ≡ 3 [ZMOD 2 * c] → n ≡ 3 [ZMOD 2 * (2 * c)],
  { intros n h,
    suffices : ∀ x k : ℕ, (f^[k] n) ≡ 3 [ZMOD 2 ^ x],
    { obtain ⟨x, h0⟩ : ∃ x : ℕ, (n - 3).nat_abs < x :=
        ⟨(n - 3).nat_abs.succ, nat.lt_succ_self _⟩,
      replace this := (this x 0).symm,
      rw [iterate_zero, id.def, int.modeq_iff_dvd] at this,
      replace h0 := lt_trans h0 (nat.lt_two_pow x),
      rw [← int.coe_nat_lt, nat.cast_pow, nat.cast_two, ← int.abs_eq_nat_abs] at h0,
      rw ← sub_eq_zero; exact int.eq_zero_of_abs_lt_dvd this h0 },
    intros x; cases x with _ x,
    intros k; rw pow_zero; exact int.modeq_one,
    induction x with x h0; intros k,
    rw [pow_one, int.modeq_iff_dvd, ← even_iff_two_dvd, int.even_sub'],
    norm_num; exact h k,
    refine this (pow_ne_zero _ two_ne_zero) (h0 k) _,
    convert h0 k.succ; rw iterate_succ' },

  ---- Prove the general result
  intros n c hc h h0,
  replace h := h.symm,
  rw int.modeq_iff_dvd at h; cases h with d h,
  rw sub_eq_iff_eq_add at h; subst h,
  symmetry; rw [int.modeq_iff_dvd, add_sub_cancel, mul_comm],
  refine mul_dvd_mul_left (2 * c) _,
  unfold f at h0,
  replace h0 : 3 ≡ 3 * ((2 * c * d + 3) / 2) [ZMOD 2 * c] :=
    h0.symm.trans (int.modeq.mul_right _ (by rw [int.modeq_iff_dvd, add_sub_cancel]; use d)).symm,
  rw [int.modeq_iff_dvd, mul_assoc, add_comm, int.add_mul_div_left _ _ two_ne_zero] at h0,
  norm_num at h0,
  rwa [← mul_sub_one, add_sub_cancel', mul_comm c, ← mul_assoc, bit1,
       mul_dvd_mul_iff_right hc, add_one_mul, dvd_add_right ⟨d, rfl⟩] at h0
end

end IMO2015N1
end IMOSL
