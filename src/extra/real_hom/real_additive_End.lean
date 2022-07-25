import data.real.sqrt

/-!
# Additive maps from ℝ to ℝ

We prove some sufficient conditions forcing an additive map from ℝ to itself to be linear.
In particular, we prove that a the endomorphism monoid End(ℝ) is trivial.
That is, the only map φ : ℝ → ℝ that is additive and multiplicative with φ(1) = 1 is the identity.

TODO:
1. If φ is continuous, then φ is linear.
2. Close `sorry` in `real_add_End_monotone` for the monotone case.
3. If φ is bounded at some non-trivial interval, then φ is linear.
-/

open real

namespace IMOSL
namespace extra

/-- An additive map from ℝ to itself that is monotone must be linear with non-negative slope. -/
theorem real_add_End_monotone (φ : ℝ →+ ℝ) (h : monotone φ) :
  ∃ C : ℝ, 0 ≤ C ∧ (φ : ℝ → ℝ) = λ x, C * x :=
begin
  use φ 1; funext x,
  have h0 : ∀ x : ℚ, φ x = φ 1 * x :=
    λ x, by rw [mul_comm, ← smul_eq_mul, ← map_rat_cast_smul φ ℝ ℝ, smul_eq_mul, mul_one],
  have h1 := h zero_le_one,
  rw map_zero at h1,
  rw and_iff_right h1,
  sorry
end

/-- An additive map from ℝ to itself that is antitone must be linear with non-positive slope. -/
theorem real_add_End_antitone (φ : ℝ →+ ℝ) (h : antitone φ) :
  ∃ C : ℝ, C ≤ 0 ∧ (φ : ℝ → ℝ) = λ x, C * x :=
begin
  replace h : monotone (⇑(-φ)) := antitone.neg h,
  replace h := real_add_End_monotone _ h,
  rcases h with ⟨C, h, h0⟩,
  change ⇑(-φ) with -φ at h0,
  rw neg_eq_iff_neg_eq at h0,
  use (-C); split,
  exact neg_nonpos.mpr h,
  funext x; rw [← h0, pi.neg_apply, neg_mul]
end

/-- There is only one ring homomorphism from ℝ to itself. -/
instance real_ring_End_unique : unique (ℝ →+* ℝ) :=
{ to_inhabited := ⟨1⟩,
  uniq := λ φ,
  begin
    obtain ⟨C, -, h⟩ : ∃ C : ℝ, 0 ≤ C ∧ (φ : ℝ → ℝ) = λ x, C * x :=
    begin
      apply real_add_End_monotone φ,
      rw ring_hom.coe_add_monoid_hom,
      intros x y h,
      rw ← sub_nonneg at h,
      have h0 := map_pow φ (sqrt (y - x)) 2,
      rw sq_sqrt h at h0,
      rw [← sub_nonneg, ← map_sub, h0],
      exact sq_nonneg _
    end,
    have h0 := congr_fun h 1,
    simp only [mul_one, map_one] at h0,
    ext x; rw [ring_hom.coe_one, id.def, h, ← h0],
    simp only [one_mul]
  end }

end extra
end IMOSL
