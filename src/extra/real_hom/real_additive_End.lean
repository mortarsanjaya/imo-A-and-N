import data.real.sqrt topology.instances.real_vector_space

/-!
# Additive ℝ-endomorphisms

We prove some sufficient conditions forcing an additive map from ℝ to itself to be linear.
In particular, we prove that a the endomorphism monoid End(ℝ) is trivial.
That is, the only map φ : ℝ → ℝ that is additive and multiplicative with φ(1) = 1 is the identity.

TODO: If φ is bounded at some non-trivial interval, then φ is linear.
-/

open real

namespace IMOSL
namespace extra

/-- Value of an additive ℝ-endomorphism on ℚ. -/
private theorem real_add_End_ratval (φ : ℝ →+ ℝ) (q : ℚ) : φ q = φ 1 * q :=
  by rw [mul_comm, ← smul_eq_mul, ← map_rat_cast_smul φ ℝ ℝ, smul_eq_mul, mul_one]

/-- An additive map from ℝ to itself that is continuous must be linear. -/
theorem real_add_End_continuous (φ : ℝ →+ ℝ) (h : continuous φ) : (φ : ℝ → ℝ) = λ x, φ 1 * x :=
begin
  funext x,
  rw [mul_comm, ← smul_eq_mul, ← add_monoid_hom.map_real_smul φ h, smul_eq_mul, mul_one]
end

/-- An additive map from ℝ to itself that is monotone must be linear with non-negative slope. -/
theorem real_add_End_monotone (φ : ℝ →+ ℝ) (h : monotone φ) : (φ : ℝ → ℝ) = λ x, φ 1 * x :=
begin
  have h0 := h zero_le_one,
  rw [map_zero, le_iff_eq_or_lt] at h0,
  have h1 := real_add_End_ratval φ,
  funext x; cases h0 with h0 h0,
  { conv at h1 { find (_ * _) { rw [← h0, zero_mul] } },
    rw [← h0, zero_mul],
    apply le_antisymm,
    { obtain ⟨q, h2⟩ := exists_rat_gt x,
      rw ← h1 q; exact h (le_of_lt h2) },
    { obtain ⟨q, h2⟩ := exists_rat_lt x,
      rw ← h1 q; exact h (le_of_lt h2) } },
  { rw [mul_comm, ← mul_inv_eq_iff_eq_mul₀ (ne_of_gt h0)],
    refine le_antisymm (le_of_forall_rat_lt_imp_le _) (le_of_forall_rat_lt_imp_le _),
    { intros q h2,
      rw [← mul_lt_mul_right h0, mul_assoc, inv_mul_cancel (ne_of_gt h0),
          mul_one, mul_comm, ← h1, ← not_le] at h2,
      rw ← not_lt; intros h3,
      exact h2 (h (le_of_lt h3)) },
    { intros q h2,
      rw [← mul_le_mul_right h0, mul_assoc, inv_mul_cancel (ne_of_gt h0), mul_one, mul_comm, ← h1],
      exact h (le_of_lt h2) } }
end

/-- An additive map from ℝ to itself that is antitone must be linear with non-positive slope. -/
theorem real_add_End_antitone (φ : ℝ →+ ℝ) (h : antitone φ) : (φ : ℝ → ℝ) = λ x, φ 1 * x :=
begin
  replace h : monotone (⇑(-φ)) := antitone.neg h,
  replace h := real_add_End_monotone _ h,
  change ⇑(-φ) with -φ at h,
  rw [neg_eq_iff_neg_eq, pi.neg_apply, pi.neg_def, eq_comm] at h,
  simp only [neg_mul, neg_neg] at h,
  exact h
end

/-- There is only one ring homomorphism from ℝ to itself. -/
instance real_ring_End_unique : unique (ℝ →+* ℝ) :=
{ to_inhabited := ⟨1⟩,
  uniq := λ φ,
  begin
    dsimp only [default],
    suffices : (φ : ℝ → ℝ) = λ x, φ 1 * x,
    { ext x,
      rw [ring_hom.coe_one, id.def, this, map_one],
      simp only [one_mul] },
    apply real_add_End_monotone φ,
    rw ring_hom.coe_add_monoid_hom,
    intros x y h,
    rw ← sub_nonneg at h,
    have h0 := map_pow φ (sqrt (y - x)) 2,
    rw sq_sqrt h at h0,
    rw [← sub_nonneg, ← map_sub, h0],
    exact sq_nonneg _
  end }

end extra
end IMOSL
