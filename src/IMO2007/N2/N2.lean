import ring_theory.int.basic data.nat.parity number_theory.legendre_symbol.quadratic_reciprocity

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

/-- Final solution, part 2 -/
theorem final_solution_part2 (p : ℕ) [fact p.prime] :
  ∃ a : zmod p, a ^ 8 = 16 :=
begin
  rw [bit0, ← two_mul]; simp only [pow_mul],
  have X : (2 : zmod p) ^ 4 = 16 := by norm_num,
  rw ← X; clear X,
  by_cases h : is_square (-1 : zmod p),

  ---- Case 1: `-1` is a square mod `p`.
  { cases h with i h,
    rw ← sq at h,
    use 1 + i; rw [add_sq', one_pow, ← h, add_neg_self, zero_add, mul_one, mul_pow],
    change _ * i ^ (2 + 2) = _,
    rw [← two_mul, pow_mul, ← h, neg_pow_bit0, one_pow, mul_one] },

  by_cases h0 : is_square (2 : zmod p),

  ---- Case 2: `2` is a square mod `p`.
  { cases h0 with a h0,
    use a; rw [sq, ← h0] },

  ---- Case 3: `-1` and `2` are not squares mod `p`.
  { rw [← int.cast_one, ← int.cast_neg, ← legendre_sym.eq_neg_one_iff] at h,
    rw [← int.cast_two, ← legendre_sym.eq_neg_one_iff] at h0,
    suffices : (2 : zmod p) ≠ 0,
    { replace h : legendre_sym p (-2) = 1 :=
        by rw [← neg_one_mul, legendre_sym.mul, h, h0, neg_mul_neg, mul_one],
      rw [← neg_ne_zero, ← int.cast_two, ← int.cast_neg] at this,
      rw [legendre_sym.eq_one_iff p this, int.cast_neg, int.cast_two] at h,
      cases h with a h,
      use a; rw [sq, ← h, neg_pow_bit0] },

    -- Now it remains to show that `-2 ≢ 0 mod p`
    apply ring.two_ne_zero,
    contrapose! h0; rw ring_char.eq (zmod p) p at h0,
    simp_rw [h0]; suffices : legendre_sym 2 2 = 0,
      rw [this, ne.def, zero_eq_neg]; exact one_ne_zero,
    rw [legendre_sym.eq_zero_iff, int.cast_two],
    exact char_two.two_eq_zero }
end

end IMO2007N2
end IMOSL
