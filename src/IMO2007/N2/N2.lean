import ring_theory.int.basic algebra.gcd_monoid.basic data.nat.parity

/-! # IMO 2007 N2 -/

namespace IMOSL
namespace IMO2007N2

private lemma lem1 {b n : ℕ} (h : ∃ c : ℤ, ((b ^ 2 : ℕ) : ℤ) ∣ b - c ^ n) :
  ∃ c : ℤ, (b : ℤ) = c ^ n :=
begin
  suffices : ∃ c : ℤ, associated (c ^ n) b,
  { cases this with c this,
    rw int.associated_iff at this,
    cases this with this this,
    exact ⟨c, this.symm⟩,
    rcases b.eq_zero_or_pos with rfl | hb,
    use c; rw [this, nat.cast_zero, neg_zero],
    use (-c); rw [neg_pow, this, odd.neg_one_pow, neg_one_mul, neg_neg],
    rw nat.odd_iff_not_even; intros h0,
    refine not_lt_of_le (even.pow_nonneg h0 c) _,
    rwa [this, right.neg_neg_iff, int.coe_nat_pos] },
  rcases h with ⟨c, d, h⟩,
  rw [nat.cast_pow, sq, mul_assoc, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', ← mul_one_sub] at h,
  refine exists_associated_pow_of_mul_eq_pow (int.is_unit_iff.mpr _) h; left,
  rw [← int.coe_gcd, nat.cast_eq_one, int.gcd_eq_one_iff_coprime],
  refine ⟨d, 1, _⟩,
  rw [one_mul, mul_comm, add_sub_cancel'_right]
end



/-- Final solution -/
theorem final_solution {b n : ℕ} (h : ∀ k : ℕ, ∃ c : ℤ, (k : ℤ) ∣ b - c ^ n) :
  ∃ c : ℤ, (b : ℤ) = c ^ n := lem1 (h (b ^ 2))

end IMO2007N2
end IMOSL
