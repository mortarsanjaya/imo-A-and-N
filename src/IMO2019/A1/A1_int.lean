import IMO2019.A1.A1_general data.int.basic algebra.algebra.basic tactic.ring

/-! # IMO 2019 A1 (P1), Integer Version -/

namespace IMOSL
namespace IMO2019A1

open function

def fn_eq_int (g : ℤ → ℤ) (s : ℤ) (f : ℤ → ℤ) := ∀ x y : ℤ, f (g x) + s * f y = f (f (x + y))



private lemma intEnd_eq_mul_left (s : ℤ) : ⇑(s : add_monoid.End ℤ) = λ x, s * x :=
  by funext; rw [← int.smul_one_eq_coe, add_monoid_hom.coe_smul,
                 add_monoid.coe_one, pi.smul_apply, id.def, smul_eq_mul]

private lemma intEnd_eq_coe_int (φ : add_monoid.End ℤ) : φ = (φ 1 : add_monoid.End ℤ) :=
begin
  apply add_monoid_hom.ext_int,
  rw intEnd_eq_mul_left; simp only [mul_one]
end

private lemma intEnd_inj_iff (s : ℤ) : injective (s : add_monoid.End ℤ) ↔ s ≠ 0 :=
begin
  rw [intEnd_eq_mul_left, injective]; split,
  rintros h rfl,
  replace h := @h 1 0 (by rw [zero_mul, zero_mul]),
  exact one_ne_zero h,
  intros h a b h0,
  rwa [mul_right_inj' h] at h0
end

private lemma intEnd_cast_inj (s t : ℤ) : (s : add_monoid.End ℤ) = t ↔ s = t :=
begin
  symmetry; split,
  rintros rfl; refl,
  intros h,
  replace h : (s : add_monoid.End ℤ) 1 = (t : add_monoid.End ℤ) 1 := by rw h,
  simp only [intEnd_eq_mul_left, mul_one] at h,
  exact h
end

private lemma feq_int_iff_feq_gen (g : ℤ → ℤ) (s : ℤ) (f : ℤ → ℤ) :
  fn_eq_int g s f ↔ fn_eq g (s : add_monoid.End ℤ) f :=
begin
  dsimp only [fn_eq_int, fn_eq],
  conv_rhs { find ((s : add_monoid.End ℤ) _) { rw intEnd_eq_mul_left } }
end



/-- Final solution for the "general" integer case. -/
theorem final_solution_int {g : ℤ → ℤ} (g0_eq_0 : g 0 = 0) {s : ℤ} (s_ne_0 : s ≠ 0) (f : ℤ → ℤ) :
  fn_eq_int g s f ↔ f = 0 ∨ ((g = λ x, s * x) ∧ ∃ C : ℤ, f = λ x, s * x + C) :=
begin
  symmetry; split,
  rintros (rfl | ⟨rfl, C, rfl⟩) x y; simp,
  ring,
  rintros h,
  rw [feq_int_iff_feq_gen, final_solution_general g0_eq_0 (by rwa intEnd_inj_iff)] at h,
  rcases h with ⟨φ, C, rfl, h, h0, h1⟩,
  rw [intEnd_eq_coe_int (φ ^ 2), intEnd_eq_coe_int (s * φ), sq, intEnd_cast_inj] at h0,
  simp only [comp_app, add_monoid.coe_mul] at h0,
  have h2 := intEnd_eq_coe_int φ,
  nth_rewrite 0 h2 at h0,
  rw [intEnd_eq_mul_left, intEnd_eq_mul_left, mul_eq_mul_right_iff] at h0,
  cases h0 with h0 h0; rw h0 at h2,
  { right; split,
    funext x,
    replace h : (φ ∘ g) x = ((s : add_monoid.End ℤ) * φ) x := by rw h,
    rwa [comp_app, add_monoid.coe_mul, comp_app, h2, intEnd_eq_mul_left,
         mul_eq_mul_left_iff, or_iff_left s_ne_0] at h,
    use C; funext x,
    rw [pi.add_apply, const_apply, h2, intEnd_eq_mul_left] },
  { rw int.cast_zero at h2; subst h2,
    rw [intEnd_eq_mul_left, add_monoid_hom.zero_apply, zero_eq_mul, or_iff_right s_ne_0] at h1,
    left; rw [h1, pi.const_zero, add_zero]; refl }
end

/-- Final solution for the original case -/
theorem final_solution_original (f : ℤ → ℤ) :
    fn_eq_int (λ x, 2 * x) 2 f ↔ (f = 0 ∨ ∃ C : ℤ, f = λ x, 2 * x + C) :=
  by rw [final_solution_int (mul_zero 2) two_ne_zero, eq_self_iff_true, true_and]

end IMO2019A1
end IMOSL
