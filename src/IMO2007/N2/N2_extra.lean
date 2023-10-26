import number_theory.legendre_symbol.quadratic_char.basic

/-! # IMO 2007 N2, Extra Version -/

namespace IMOSL
namespace IMO2007N2

variables {F : Type*} [field F] [fintype F] [decidable_eq F]

lemma is_square_or_mul (a b : F) :
  is_square a ∨ is_square b ∨ is_square (a * b) :=
have X : ∀ {a : F}, quadratic_char F a = -1 ↔ ¬is_square a :=
  λ a, quadratic_char_neg_one_iff_not_is_square,
have h : (-1 : ℤ) < -1 * -1 := neg_one_lt_zero.trans int.one_pos,
or_iff_not_imp_left.mpr $ λ h0, or_iff_not_imp_left.mpr $ λ h1, by_contra $ λ h2,
  absurd (X.mpr h2) (((quadratic_char F).map_mul a b).symm.trans_gt $
    h.trans_eq $ congr_arg2 _ (X.mpr h0).symm (X.mpr h1).symm).ne.symm



/-- Final solution, extra -/
theorem final_solution_extra [decidable_eq F] : ∃ a : F, a ^ 8 = 16 :=
---- Reduce to finding a square `c : F` such that `c ^ 4 = 2 ^ 4`
suffices ∃ a : F, is_square a ∧ a ^ 4 = 2 ^ 4,
  from exists.elim this $ λ a h, exists.elim h.1 $ λ c h0,
    ⟨c, (pow_mul c 2 4).trans $ (sq c).symm ▸ h0 ▸ h.2.trans (by ring)⟩,
---- Find such `c`
(is_square_or_mul (-1 : F) (2 : F)).elim
-- Case 1: `-1` is a square mod `p`
(λ h, exists.elim h $ λ i h, ⟨2 * i,
  ⟨1 + i, by rw [add_mul_self_eq, mul_one, mul_one, ← h, add_neg_cancel_comm]⟩,
  suffices i ^ 4 = 1, from (mul_pow 2 i 4).trans $ this.symm ▸ mul_one _,
  (pow_mul i 2 2).trans $ (sq i).symm ▸ h ▸ neg_one_sq⟩)
$ λ h, h.elim
-- Case 2: `2` is a square mod `p`
(λ h, ⟨2, h, rfl⟩)
-- Case 3: `-2` is a square mod `p`
(λ h, ⟨(-1) * 2, h, (neg_one_mul (2 : F)).symm ▸ neg_pow_bit0 _ 2⟩)

end IMO2007N2
end IMOSL
