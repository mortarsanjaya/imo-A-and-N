import number_theory.legendre_symbol.quadratic_char

/-! # IMO 2007 N2, Extra Version -/

namespace IMOSL
namespace IMO2007N2

variables {F : Type*} [field F] [fintype F]

private lemma not_is_square_ne_zero {a : F} (h : ¬is_square a) : a ≠ 0 :=
  by rintros rfl; exact h (is_square_zero F)

private lemma is_square_or_mul [decidable_eq F] (a b : F) :
  is_square a ∨ is_square b ∨ is_square (a * b) :=
begin
  rw [or_iff_not_imp_left, or_iff_not_imp_left]; intros h h0,
  have h1 : a * b ≠ 0 := mul_ne_zero (not_is_square_ne_zero h) (not_is_square_ne_zero h0),
  rw ← quadratic_char_neg_one_iff_not_is_square at h h0,
  rw [← quadratic_char_one_iff_is_square h1, map_mul, h0, h, neg_mul_neg, mul_one]
end



/-- Final solution, part 2 -/
theorem final_solution_part2 [decidable_eq F] : ∃ a : F, a ^ 8 = 16 :=
begin
  ---- Reduce to finding a square `c : F` such that `c ^ 4 = 16`
  suffices : ∃ a : F, is_square a ∧ a ^ 4 = 2 ^ 4,
  { rcases this with ⟨_, ⟨c, rfl⟩, h⟩,
    refine ⟨c, _⟩,
    rw [bit0, ← two_mul, pow_mul, sq, h],
    norm_num },

  ---- If `2` or `-2` is a square mod `p`, we are easily done
  rcases (is_square_or_mul (-1 : F) (2 : F)).symm with (h | h) | ⟨i, h⟩,
  exact ⟨2, h, rfl⟩,
  exact ⟨(-1) * 2, h, by rw [neg_one_mul, neg_pow_bit0]⟩,
  
  -- The case where `-1` is a square mod `p` remains
  rw ← sq at h; refine ⟨2 * i, ⟨1 + i, _⟩, _⟩,
  rw [← sq, add_sq', one_pow, ← h, add_neg_self, zero_add, mul_one],
  rw [mul_comm, mul_pow]; change i ^ (2 * 2) * 2 ^ 4 = 2 ^ 4,
  rw [pow_mul, ← h, neg_one_sq, one_mul]
end

end IMO2007N2
end IMOSL
