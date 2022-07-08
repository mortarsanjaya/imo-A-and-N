import IMO2019.A1.A1_general data.int.basic algebra.algebra.basic

/-!
# IMO 2019 A1 (P1), Integer Version

Let g : ℤ → ℤ be a function with g(0) = 0, and let s be an integer with s ≠ 0.
Determine all functions f : ℤ → ℤ such that, for all x, y ∈ ℤ,
  f(g(x)) + s f(y) = f(f(x + y)).

## Answer

1. g ≠ x ↦ sx: f = 0 only.
2. g = x ↦ sx: f = 0 and f = x ↦ sx + C for any choice of C ∈ ℤ.

## Solution

The ring of endomorphisms of ℤ is isomorphic to ℤ itself.
So, that means we can write φ(x) = kx and T(x) = sx for some integer m, r, and s.
The equation Tφ = φ^2 implies ks = k^2, so either m = s or m = 0.
The equation φ ∘ g = Tφ reads as k g(x) = skx for all x ∈ ℤ.
Thus, for g ≠ x ↦ sx, we have k = 0, and the equation φ(C) = T(C) reads as sC = 0 → C + 0.
For g = x ↦ sx, any choice of C works.

## Implementation details

We just need to give a homomorphism ℤ →+* End(ℤ).
We can in fact give an isomorphism, but we do not need to do that.
-/

open function

namespace IMOSL
namespace IMO2019A1

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



theorem final_solution_int {g : ℤ → ℤ} (g0_eq_0 : g 0 = 0) {s : ℤ} (s_ne_0 : s ≠ 0) 
    (h : g ≠ λ x, s * x) (f : ℤ → ℤ) :
  fn_eq_int g s f ↔ f = 0 :=
begin
  symmetry; split,
  rintros rfl x y; simp only [pi.zero_apply, mul_zero, add_zero],
  intros h0,
  rw [feq_int_iff_feq_gen, final_solution_general g0_eq_0 (by rwa intEnd_inj_iff)] at h0,
  rcases h0 with ⟨φ, C, rfl, h0, h1, h2⟩,
  rw [intEnd_eq_coe_int (φ ^ 2), intEnd_eq_coe_int (s * φ), sq, intEnd_cast_inj] at h1,
  simp only [comp_app, add_monoid.coe_mul] at h1,
  have h3 := intEnd_eq_coe_int φ,
  nth_rewrite 0 h3 at h1,
  rw [intEnd_eq_mul_left, intEnd_eq_mul_left, mul_eq_mul_right_iff] at h1,
  cases h1 with h1 h1; rw h1 at h3,
  { exfalso; apply h; funext n,
    replace h0 : (φ ∘ g) n = ((s : add_monoid.End ℤ) * φ) n := by rw h0,
    rwa [comp_app, add_monoid.coe_mul, comp_app, h3, intEnd_eq_mul_left,
         mul_eq_mul_left_iff, or_iff_left s_ne_0] at h0 },
  { rw int.cast_zero at h3; subst h3,
    rw [intEnd_eq_mul_left, add_monoid_hom.zero_apply, zero_eq_mul, or_iff_right s_ne_0] at h2,
    rw [h2, pi.const_zero, add_zero]; refl }
end


theorem final_solution_int_case_r_eq_s {s : ℤ} (s_ne_0 : s ≠ 0) (f : ℤ → ℤ) :
  fn_eq_int (λ x, s * x) s f ↔ (f = 0 ∨ ∃ C : ℤ, f = λ x, s * x + C) :=
begin
  symmetry; split,
  rintros (rfl | ⟨C, rfl⟩) x y; simp,
  ring,
  rintros h,
  rw [feq_int_iff_feq_gen, final_solution_general (mul_zero s) (by rwa intEnd_inj_iff)] at h,
  rcases h with ⟨φ, C, rfl, -, h, h0⟩,
  rw [intEnd_eq_coe_int (φ ^ 2), intEnd_eq_coe_int (s * φ), sq, intEnd_cast_inj] at h,
  simp only [comp_app, add_monoid.coe_mul] at h,
  have h1 := intEnd_eq_coe_int φ,
  nth_rewrite 0 h1 at h,
  rw [intEnd_eq_mul_left, intEnd_eq_mul_left, mul_eq_mul_right_iff] at h,
  cases h with h h; rw h at h1,
  { right; use C; funext x,
    rw [pi.add_apply, const_apply, h1, intEnd_eq_mul_left] },
  { rw int.cast_zero at h1; subst h1,
    rw [intEnd_eq_mul_left, add_monoid_hom.zero_apply, zero_eq_mul, or_iff_right s_ne_0] at h0,
    left; rw [h0, pi.const_zero, add_zero]; refl }
end


theorem final_solution_original (f : ℤ → ℤ) :
    fn_eq_int (λ x, 2 * x) 2 f ↔ (f = 0 ∨ ∃ C : ℤ, f = λ x, 2 * x + C) :=
  final_solution_int_case_r_eq_s two_ne_zero f

end IMO2019A1
end IMOSL
