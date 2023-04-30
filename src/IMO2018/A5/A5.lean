import algebra.order.positive.field algebra.module.submodule.basic

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
    by simp_rw [pi.add_apply, smul_add]; rw [h x y, h0 x y, add_add_add_comm],
  zero_mem' := λ x y, by simp_rw pi.zero_apply; rw [smul_zero, zero_add],
  smul_mem' := λ c f h x y, by simp_rw [pi.smul_apply, smul_comm _ c, h x, ← smul_add] }

private lemma smul_vec_is_good (v : V) :
  good (λ x : {x : F // 0 < x}, (x : F) • v) :=
  λ x y, by simp_rw [positive.coe_mul, positive.coe_inv, ← smul_smul, ← add_smul]

private lemma inv_smul_vec_is_good (v : V) :
  good (λ x : {x : F // 0 < x}, (x⁻¹ : F) • v) :=
  λ x y, by simp_rw [positive.coe_mul, mul_inv, positive.coe_inv, inv_inv, ← smul_smul];
    rw [← add_smul, add_comm (x : F)]
    
private lemma smul_add_inv_smul_is_good (v1 v2 : V) :
  good (λ x : {x : F // 0 < x}, (x : F) • v1 + (x⁻¹ : F) • v2) :=
  (good_space F V).add_mem (smul_vec_is_good v1) (inv_smul_vec_is_good v2)

private lemma exists_smul_add_inv_smul_two_eq {a b : {x : F // 0 < x}} (h : a ≠ b) (v1 v2 : V) :
 ∃ w1 w2 : V, (a : F) • w1 + (a : F)⁻¹ • w2 = v1 ∧ (b : F) • w1 + (b : F)⁻¹ • w2 = v2 :=
begin
  set S := {x : F // 0 < x},
  let c : F := a * b⁻¹ - b * a⁻¹,
  rsuffices ⟨h0, h1⟩ : c ≠ 0 ∧ ∃ w1 w2 : V,
    (a : F) • w1 + (a : F)⁻¹ • w2 = c • v1 ∧ (b : F) • w1 + (b : F)⁻¹ • w2 = c • v2,
  { rcases h1 with ⟨w1, w2, h1, h2⟩,
    refine ⟨c⁻¹ • w1, c⁻¹ • w2, _, _⟩;
      simp_rw [smul_smul, mul_comm _ c⁻¹, ← smul_smul];
      rwa [← smul_add, inv_smul_eq_iff₀ h0] },
  dsimp only [c]; clear c; split,

  ---- `ab⁻¹ ≠ ba⁻¹`
  { simp_rw [← positive.coe_inv, ← positive.coe_mul],
    rw [ne.def, sub_eq_zero, set_coe.ext_iff, ← mul_inv_eq_one, mul_inv_rev, inv_inv, ← sq],
    revert h; rw [ne.def, ← mul_inv_eq_one, not_imp_not],
    exact (pow_eq_one_iff two_ne_zero).mp },

  ---- `f` good with `f(a) = (ab⁻¹ - ba⁻¹) v₁` and `f(b) = (ab⁻¹ - ba⁻¹) v₂`
  { refine ⟨(b : F)⁻¹ • v1 - (a : F)⁻¹ • v2, (a : F) • v2 - (b : F) • v1, _⟩,
    replace h : (a : F) ≠ 0 := ne_of_gt a.2,
    generalize_hyp : (a : F) = x at h ⊢,
    have h0 : (b : F) ≠ 0 := ne_of_gt b.2,
    generalize_hyp : (b : F) = y at h0 ⊢,
    clear a b S; simp_rw [smul_sub, smul_smul]; split,
    rw [mul_inv_cancel h, inv_mul_cancel h, sub_add_sub_cancel, ← sub_smul, mul_comm y],
    rw [mul_inv_cancel h0, inv_mul_cancel h0, sub_add_sub_cancel', ← sub_smul, mul_comm x] }
end

private lemma good_two_eq_zero {f : {x : F // 0 < x} → V} (h : good f)
  {a b : {x : F // 0 < x}} (h0 : a ≠ b) (h1 : f a = 0) (h2 : f b = 0) :
  f = 0 :=
begin
  have h3 : ∀ u : {x : F // 0 < x}, f u = 0 → ∀ x : {x : F // 0 < x}, f (u ^ 2 * x) = -f x⁻¹ :=
    λ u h3 x, by replace h := h (u * x) u; rwa [h3, smul_zero, mul_inv_rev,
      inv_mul_cancel_right, mul_right_comm, ← sq, eq_comm, add_eq_zero_iff_eq_neg] at h,
  replace h3 : ∀ x : {x : F // 0 < x}, f ((a * b⁻¹) ^ 2 * x) = f x :=
    λ x, by rw [mul_pow, mul_assoc, h3 a h1, ← h3 b h2, inv_pow, mul_inv_cancel_left],
  rw [ne.def, ← mul_inv_eq_one] at h0,
  replace h0 : (a * b⁻¹) ^ 2 ≠ 1 := λ h4, h0 ((pow_eq_one_iff two_ne_zero).mp h4),
  clear h1 h2; generalize_hyp : (a * b⁻¹) ^ 2 = c at h0 h3,

  funext x; replace h := h c (c * x),
  rw [h3 (c * x), h3, inv_mul_cancel_left, ← sub_eq_zero,
      ← two_smul F, ← sub_smul, smul_eq_zero, sub_eq_zero] at h,
  revert h; clear h3; refine (or_iff_right (λ h3, _)).mp,
  apply_fun has_mul.mul (c : F) at h3,
  have h1 : 0 < (c : F) := c.2,
  rw [mul_add, mul_inv_cancel (ne_of_gt h1), mul_two, ← eq_sub_iff_add_eq,
      add_sub_assoc, ← sub_eq_iff_eq_add', ← mul_sub_one, mul_left_eq_self₀,
      sub_eq_zero, or_self, ← positive.coe_one, subtype.coe_inj] at h3,
  exact h0 h3
end



/-- Final solution -/
theorem final_solution (f : {x : F // 0 < x} → V) :
  good f ↔ ∃ v1 v2 : V, f = λ x, (x : F) • v1 + (x⁻¹ : F) • v2 :=
begin
  symmetry; refine ⟨λ h, _, λ h, _⟩,
  rcases h with ⟨v1, v2, rfl⟩,
  exact smul_add_inv_smul_is_good v1 v2,
  obtain ⟨a, b, h0⟩ : ∃ a b : {x : F // 0 < x}, a ≠ b :=
    ⟨⟨2, two_pos⟩, ⟨1, one_pos⟩, ne_of_gt (by rw subtype.mk_lt_mk; exact one_lt_two)⟩,
  obtain ⟨v1, v2, h1, h2⟩ := exists_smul_add_inv_smul_two_eq h0 (f a) (f b),
  rw [eq_comm, ← sub_eq_zero] at h1 h2,
  refine ⟨v1, v2, sub_eq_zero.mp (good_two_eq_zero _ h0 h1 h2)⟩,
  exact (good_space F V).sub_mem h (smul_add_inv_smul_is_good v1 v2)
end

end IMO2018A5
end IMOSL
