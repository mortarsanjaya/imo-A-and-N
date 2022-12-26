import algebra.order.positive.field algebra.module.basic algebra.module.submodule.basic

/-! # IMO 2018 A5 -/

namespace IMOSL
namespace IMO2018A5

variables {F V : Type*} [linear_ordered_field F] [add_comm_group V] [module F V]

def good (f : {x : F // 0 < x} → V) :=
  ∀ x y : {x : F // 0 < x}, (x + x⁻¹ : F) • f y = f (x * y) + f (x⁻¹ * y)



private def good_space (F V : Type*) [linear_ordered_field F] [add_comm_group V] [module F V] :
  submodule F ({x : F // 0 < x} → V) :=
{ carrier := set_of good,
  add_mem' := λ f g h h0 x y,
    by simp_rw [pi.add_apply, smul_add, h x y, h0 x y, add_add_add_comm _ (g (x * y))],
  zero_mem' := λ x y, by simp_rw [pi.zero_apply, smul_zero, zero_add],
  smul_mem' := λ c f h x y, by simp_rw [pi.smul_apply, smul_comm _ c, h x, ← smul_add] }

private lemma smul_vec_is_good (v : V) :
  (λ x : {x : F // 0 < x}, (x : F) • v) ∈ good_space F V :=
  λ x y, by simp_rw [positive.coe_mul, positive.coe_inv, ← smul_smul, ← add_smul]

private lemma inv_smul_vec_is_good (v : V) :
    (λ x : {x : F // 0 < x}, (x⁻¹ : F) • v) ∈ good_space F V :=
  λ x y, by simp_rw [positive.coe_mul, mul_inv, positive.coe_inv, inv_inv, ← smul_smul];
    rw [← add_smul, add_comm (x : F)]
    
private lemma smul_vec_add_inv_smul_vec_is_good (v1 v2 : V) :
    good (λ x : {x : F // 0 < x}, (x : F) • v1 + (x⁻¹ : F) • v2) :=
  (good_space F V).add_mem (smul_vec_is_good v1) (inv_smul_vec_is_good v2)



/-- Final solution -/
theorem final_solution {F V : Type*} [linear_ordered_field F] [add_comm_group V] [module F V] :
  ∀ f : {x : F // 0 < x} → V, good f ↔ ∃ v1 v2 : V, f = λ x, (x : F) • v1 + (x⁻¹ : F) • v2 :=
begin
  ---- First solve the `←` direction.
  intros f; symmetry; refine ⟨λ h, _, λ h, _⟩,
  rcases h with ⟨v1, v2, rfl⟩,
  exact smul_vec_add_inv_smul_vec_is_good v1 v2,

  ---- Now reduce to showing that, if `f(1) = f(2) = 0`, then `f = 0`
  use [-(1 / 3 : F) • f 1 + (2 / 3 : F) • f 2, ((2 + 2) / 3 : F) • f 1 + -(2 / 3 : F) • f 2],
  rw ← sub_eq_zero; revert h f,
  suffices : ∀ f : {x : F // 0 < x} → V, good f → (f 1 = 0 ∧ f 2 = 0) → f = 0,
  { intros f h,
    refine this _ ((good_space F V).sub_mem h (smul_vec_add_inv_smul_vec_is_good _ _)) _,
    set g := λ x : {x : F // 0 < x}, (x : F) • (-(1 / 3 : F) • f 1 + (2 / 3 : F) • f 2) +
      (x : F)⁻¹ • (((2 + 2) / 3 : F) • f 1 + (-(2 / 3 : F) • f 2)) with hg,
    simp_rw [smul_add, smul_smul, add_add_add_comm _ (_ • f 2), ← add_smul, mul_neg,
      add_comm (- (_ * (1 / 3 : F))), ← sub_eq_add_neg, ← mul_div_assoc, ← sub_div, mul_one] at hg,
    have h0 : (2 + 2 - 1 : F) / 3 = 1 := by norm_num,
    simp_rw [hg, pi.sub_apply, sub_eq_zero]; split,
    rw [positive.coe_one, inv_one, sub_self, zero_div, zero_smul, add_zero, one_mul, h0, one_smul],
    change ((2 : {x : F // 0 < x}) : F) with (2 : F),
    rw [← two_mul, ← mul_assoc, inv_mul_cancel (two_ne_zero : (2 : F) ≠ 0), one_mul,
        sub_self, zero_div, zero_smul, zero_add, two_mul, h0, one_smul] },

  ---- Finally, show that, if `f(1) = f(2) = 0`, then `f = 0`
  rintros f h h0,
  replace h0 : ∀ t : {x : F // 0 < x}, f (2 * 2 * t) = f t :=
  begin
    intros t,
    have h2 := h (2 * t) 2,
    rw [h0.2, smul_zero, mul_inv_rev, inv_mul_cancel_right, mul_right_comm] at h2,
    replace h := h t 1,
    rwa [h0.1, smul_zero, mul_one, mul_one, h2, add_left_inj] at h
  end,

  funext t; replace h := h (2 * 2) t,
  rw [h0, ← h0 ((2 * 2)⁻¹ * t), mul_inv_cancel_left, ← sub_eq_zero,
      ← two_smul F, ← sub_smul, smul_eq_zero, positive.coe_mul, sub_eq_zero] at h,
  revert h; refine (or_iff_right (ne_of_gt _)).mp,
  rw ← sq; refine lt_add_of_lt_of_nonneg _ (inv_nonneg.mpr (sq_nonneg _)),
  change (2 : F) < (2 : F) ^ 2,
  norm_num
end

end IMO2018A5
end IMOSL