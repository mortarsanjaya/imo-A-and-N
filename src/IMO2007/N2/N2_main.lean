import ring_theory.int.basic data.nat.parity

/-! # IMO 2007 N2 -/

namespace IMOSL
namespace IMO2007N2

/-- Final solution, part 1 -/
theorem final_solution_part1 {b n : ℕ} (h : 0 < b)
    (h0 : ∀ k : ℕ, 0 < k → ∃ c : ℤ, (k : ℤ) ∣ b - c ^ n) :
  ∃ a : ℤ, (b : ℤ) = a ^ n :=
begin
  replace h0 := h0 (b ^ 2) (pow_pos h 2),
  suffices h1 : ∃ c : ℤ, associated (c ^ n) b,
  { cases h1 with c h1,
    rw int.associated_iff at h1,
    cases h1 with h1 h1,
    exact ⟨c, h1.symm⟩,
    use (-c); rw [neg_pow, h1, odd.neg_one_pow, neg_one_mul, neg_neg],
    rw nat.odd_iff_not_even; intros h0,
    refine not_lt_of_le (even.pow_nonneg h0 c) _,
    rwa [h1, right.neg_neg_iff, int.coe_nat_pos] },

  rcases h0 with ⟨c, d, h0⟩,
  rw [nat.cast_pow, sq, mul_assoc, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', ← mul_one_sub] at h0,
  refine exists_associated_pow_of_mul_eq_pow (int.is_unit_iff.mpr _) h0; left,
  rw [← int.coe_gcd, nat.cast_eq_one, int.gcd_eq_one_iff_coprime],
  refine ⟨d, 1, _⟩,
  rw [one_mul, mul_comm, add_sub_cancel'_right]
end

end IMO2007N2
end IMOSL
