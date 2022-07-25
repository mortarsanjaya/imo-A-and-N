import data.real.basic data.real.nnreal extra.real_additive_End

/-!
# Extension of function ℝ≥0 → α into an almost odd function ℝ → α

The "odd" extension g : ℝ → α of f : ℝ≥0 → α is given by g(x) = f(x) for x ≥ 0 and
  g(x) = -f(-x) for x ≤ 0. If one also has f(0) = -f(0), g is indeed an odd function.
Here, α is any type with negation.

A more useful aspect of the odd extension is when α is an additive group or a ring,
  and f is a group/ring homomorphism. Then we always have f(0) = 0, so g(0) is always odd.
Furthermore, the odd extension is also a group/ring homomorphism, except with domain ℝ.

TODO: Add a `coe_factor` lemma (any map ℝ≥0 →+* R factors through the coercion ℝ≥0 →+* ℝ)
-/

open real
open_locale nnreal classical

namespace IMOSL
namespace extra

private lemma nnabs_neg (r : ℝ) : (-r).nnabs = r.nnabs :=
  by rw [← nnreal.coe_eq, coe_nnabs, coe_nnabs, abs_neg]



section function

/-- The odd extension as a function. It is not guaranteed to be odd, however.
  For the lemmas, we assume that the negation is always involutive. -/
noncomputable def nnreal_odd_ext {α : Type*} [has_neg α] (f : ℝ≥0 → α) : ℝ → α :=
  λ x, ite (0 ≤ x) (f x.nnabs) (-f x.nnabs)

variables {α : Type*} [has_involutive_neg α]

lemma nnreal_odd_ext_of_nnreal (f : ℝ≥0 → α) (x : ℝ≥0) :
    nnreal_odd_ext f (x : ℝ) = f x :=
  by simp only [nnreal_odd_ext, if_true, nnreal.zero_le_coe, nnabs_of_nonneg, to_nnreal_coe]

lemma nnreal_odd_ext_of_nonneg (f : ℝ≥0 → α) {x : ℝ} (h : 0 ≤ x) :
    nnreal_odd_ext f x = f x.nnabs :=
  by simp only [nnreal_odd_ext, if_true, h]

lemma nnreal_odd_ext_of_negative (f : ℝ≥0 → α) {x : ℝ} (h : x < 0) :
    nnreal_odd_ext f x = -f x.nnabs :=
  by rw ← not_le at h; simp only [nnreal_odd_ext, if_false, h]

/-- If α has involutive negation, then `nnreal_odd_ext` is odd except possibly at 0. -/
lemma nnreal_odd_ext_is_odd' (f : ℝ≥0 → α) {x : ℝ} (h : x ≠ 0) :
  nnreal_odd_ext f (-x) = -nnreal_odd_ext f x :=
begin
  simp only [nnreal_odd_ext, neg_nonneg, nnabs_neg],
  rw ne_iff_lt_or_gt at h,
  cases h with h h,
  rw [if_neg (not_le_of_lt h), if_pos (le_of_lt h), neg_neg],
  rw [if_neg (not_le_of_lt h), if_pos (le_of_lt h)]
end

/-- If α has involutive negation and -f(0) = f(0), then `nnreal_odd_ext` is indeed odd. -/
lemma nnreal_odd_ext_is_odd (f : ℝ≥0 → α) (h : - f 0 = f 0) (x : ℝ) :
  nnreal_odd_ext f (-x) = -nnreal_odd_ext f x :=
begin
  rcases eq_or_ne x 0 with rfl | h,
  simp only [nnreal_odd_ext, if_true, le_refl, neg_zero, nnabs_of_nonneg, to_nnreal_zero, h],
  exact nnreal_odd_ext_is_odd' f h
end

end function



section add_group_hom

variables {G : Type*} [add_group G]

/-- Extension of a homomorphism ℝ≥0 →+ G to ℝ →+ G. -/
noncomputable def nnreal_add_group_hom_ext (φ : ℝ≥0 →+ G) : ℝ →+ G :=
{ to_fun := nnreal_odd_ext φ,
  map_zero' := by simp only [le_refl, nnreal_odd_ext,
    if_true, nnabs_of_nonneg, to_nnreal_zero, map_zero],
  map_add' := begin
    have odd_ext_neg : ∀ x : ℝ, nnreal_odd_ext φ (-x) = -nnreal_odd_ext φ x :=
      nnreal_odd_ext_is_odd φ (by rw [map_zero, neg_zero]),
    suffices : ∀ x y : ℝ, 0 ≤ y →
      nnreal_odd_ext ⇑φ (x + y) = nnreal_odd_ext ⇑φ x + nnreal_odd_ext ⇑φ y,
    { intros x y,
      cases le_total 0 y with h h,
      exact this x y h,
      rw [← add_left_inj (nnreal_odd_ext ⇑φ (-y)), ← this _ _ (neg_nonneg.mpr h),
          add_neg_cancel_right, odd_ext_neg, add_neg_cancel_right] },
    have T : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      nnreal_odd_ext ⇑φ (x + y) = nnreal_odd_ext ⇑φ x + nnreal_odd_ext ⇑φ y :=
    begin
      intros x y hx hy,
      simp only [nnreal_odd_ext, hx, hy, add_nonneg, if_true, nnabs_of_nonneg],
      rw [to_nnreal_add hx hy, map_add]
    end,
    intros x y hy,
    cases le_total 0 x with hx hx,
    exact T x y hx hy,
    rw [← add_right_inj (-nnreal_odd_ext ⇑φ x), neg_add_cancel_left, ← odd_ext_neg],
    rw ← neg_nonneg at hx,
    cases le_total 0 (x + y) with hxy hxy,
    rw [← T _ _ hx hxy, neg_add_cancel_left],
    rw [← add_left_inj (-nnreal_odd_ext ⇑φ (x + y)), add_neg_cancel_right, ← odd_ext_neg,
        ← T _ _ hy (neg_nonneg.mpr hxy), neg_add_rev, add_neg_cancel_left]
  end }

noncomputable instance nnreal_add_group_hom.has_coe_to_real_add_group_hom :
  has_coe (ℝ≥0 →+ G) (ℝ →+ G) := ⟨nnreal_add_group_hom_ext⟩

end add_group_hom



section ring_hom

variables {R : Type*} [ring R]

noncomputable def nnreal_ring_hom_ext (φ : ℝ≥0 →+* R) : ℝ →+* R :=
{ map_one' := begin
    have h : 0 ≤ (1 : ℝ) := zero_le_one,
    simp only [nnreal_add_group_hom_ext, nnreal_odd_ext, ring_hom.to_add_monoid_hom_eq_coe],
    rw [if_pos h, ring_hom.coe_add_monoid_hom, nnabs_of_nonneg h, to_nnreal_one, map_one]
  end,
  map_mul' := begin
    simp only [ring_hom.to_add_monoid_hom_eq_coe,
      nnreal_add_group_hom_ext, ring_hom.coe_add_monoid_hom],
    have X := nnreal_odd_ext_is_odd φ (by rw [map_zero, neg_zero]),
    suffices : ∀ x y : ℝ, 0 ≤ y →
      nnreal_odd_ext ⇑φ (x * y) = nnreal_odd_ext ⇑φ x * nnreal_odd_ext ⇑φ y,
    { intros x y,
      cases le_total 0 y with h h,
      exact this x y h,
      rw [← neg_neg y, X, mul_neg, X, this _ _ (neg_nonneg.mpr h), mul_neg] },
    have T : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      nnreal_odd_ext ⇑φ (x * y) = nnreal_odd_ext ⇑φ x * nnreal_odd_ext ⇑φ y :=
    begin
      intros x y hx hy,
      simp only [nnreal_odd_ext, hx, hy, mul_nonneg, if_true, nnabs_of_nonneg],
      rw [to_nnreal_mul hx, map_mul]
    end,
    intros x y hy,
    cases le_total 0 x with hx hx,
    exact T x y hx hy,
    rw [← neg_neg x, X, neg_mul, X, T _ _ (neg_nonneg.mpr hx) hy, neg_mul]
  end,
  .. nnreal_add_group_hom_ext φ.to_add_monoid_hom }

namespace nnreal_ring_hom

noncomputable instance has_coe_to_real_ring_hom :
  has_coe (ℝ≥0 →+* R) (ℝ →+* R) := ⟨nnreal_ring_hom_ext⟩

lemma coe_fn_apply (φ : ℝ≥0 →+* R) (x : ℝ≥0) : (φ : ℝ →+* R) x = φ x :=
  by change ⇑(φ : ℝ →+* R) with nnreal_odd_ext φ; rw nnreal_odd_ext_of_nnreal

lemma coe_unique {φ : ℝ≥0 →+* R} {ρ : ℝ →+* R}
  (h : ∀ x : ℝ≥0, ρ x = φ x) : ρ = (φ : ℝ →+* R) :=
begin
  ext x,
  change ⇑(φ : ℝ →+* R) with nnreal_odd_ext φ,
  cases le_or_lt 0 x with h0 h0,
  rw [nnreal_odd_ext_of_nonneg _ h0, ← h, coe_nnabs, abs_eq_self.mpr h0],
  rw [nnreal_odd_ext_of_negative _ h0, ← h, coe_nnabs,
      abs_eq_neg_self.mpr (le_of_lt h0), map_neg, neg_neg]
end

lemma coe_inj (φ ρ : ℝ≥0 →+* R) : (φ : ℝ →+* R) = (ρ : ℝ →+* R) ↔ φ = ρ :=
begin
  symmetry; split,
  rintros rfl; refl,
  intros h; ext x,
  rw [← coe_fn_apply, h, coe_fn_apply]
end

instance to_real_ring_hom_unique : unique (ℝ≥0 →+* ℝ) :=
{ default := nnreal.to_real_hom,
  uniq := λ φ, by rw [← coe_inj, eq_iff_true_of_subsingleton]; trivial }

end nnreal_ring_hom

end ring_hom

end extra
end IMOSL
