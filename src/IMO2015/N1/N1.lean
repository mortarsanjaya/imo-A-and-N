import data.int.parity data.int.modeq ring_theory.coprime.lemmas

/-! # IMO 2015 N1 -/

namespace IMOSL
namespace IMO2015N1

open function

def f (n : ℤ) := n * (n / 2)

/-- Final solution -/
theorem final_solution (n : ℤ) : (∃ k : ℕ, even (f^[k] n)) ↔ n ≠ 3 :=
begin
  rw [← not_iff_not, not_not, not_exists, iff.comm],
  refine ⟨λ h, _, λ h, _⟩,
  { subst h,
    suffices : ∀ x : ℕ, f^[x] 3 = 3,
      intros x; rw this; norm_num,
    intros x; induction x with x x_ih,
    rw [iterate_zero, id.def],
    rw [iterate_succ', comp_app, x_ih]; refl },
  suffices : ∀ x k : ℕ, (f^[k] n) ≡ 3 [ZMOD 2 ^ x],
  { obtain ⟨x, h0⟩ : ∃ x : ℕ, (n - 3).nat_abs < x :=
      ⟨(n - 3).nat_abs.succ, nat.lt_succ_self _⟩,
    replace this := (this x 0).symm,
    rw [iterate_zero, id.def, int.modeq_iff_dvd] at this,
    replace h0 := lt_trans h0 (nat.lt_two_pow x),
    rw [← int.coe_nat_lt, nat.cast_pow, nat.cast_two, ← int.abs_eq_nat_abs] at h0,
    rw ← sub_eq_zero; exact int.eq_zero_of_abs_lt_dvd this h0 },
  { intros x; cases x with _ x,
    intros k; rw pow_zero; exact int.modeq_one,
    induction x with x h0; intros k,
    rw [pow_one, int.modeq_iff_dvd, ← even_iff_two_dvd, int.even_sub'],
    norm_num; exact h k,
    replace h := (h0 k).symm,
    replace h0 := h0 (k + 1),
    rw [iterate_succ', comp_app, f] at h0,
    replace h0 := int.modeq.trans h0.symm (int.modeq.mul_right _ h.symm),
    rw int.modeq_iff_dvd at h; cases h with d h,
    rw sub_eq_iff_eq_add at h,
    rw [int.modeq_iff_dvd, ← mul_sub_one, h, pow_succ, mul_assoc, add_comm,
        int.add_mul_div_left _ _ two_ne_zero, add_comm, ← pow_succ] at h0,
    norm_num at h0,
    replace h0 : 2 ^ x.succ ∣ 2 ^ x * d :=
      is_coprime.dvd_of_dvd_mul_left (is_coprime.pow_left ⟨2, -1, by norm_num⟩) h0,
    cases h0 with c h0,
    rw [pow_succ', mul_assoc, mul_eq_mul_left_iff] at h0,
    symmetry; rw [int.modeq_iff_dvd, h, add_sub_cancel],
    rcases h0 with rfl | h0,
    use c; rw [← mul_assoc, ← pow_succ'],
    exfalso; refine pow_ne_zero x _ h0; exact two_ne_zero }
end

end IMO2015N1
end IMOSL
