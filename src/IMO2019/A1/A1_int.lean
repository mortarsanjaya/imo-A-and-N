import IMO2019.A1.A1_general algebra.ring.equiv data.int.basic

namespace IMOSL
namespace IMO2019A1

/--
  IMO 2019 A1 (P1), Integer Version (G = ℤ)

  Let g : ℤ → ℤ be a function with g(0) = 0, and let s be an integer with s ≠ 0.
  Determine all functions f : ℤ → ℤ such that, for all x, y ∈ ℤ,
          f(g(x)) + s f(y) = f(f(x + y)).

  Answer:
    1. g ≠ x ↦ sx: f = 0 only.
    2. g = x ↦ sx: f = 0 and f = x ↦ sx + C for any choice of C ∈ ℤ.

  Solution:
    The ring of endomorphisms of ℤ is isomorphic to ℤ itself.
    So, that means we can write φ(x) = kx and T(x) = sx for some integer m, r, and s.
    The equation Tφ = φ^2 implies ks = k^2, so either m = s or m = 0.
    The equation φ ∘ g = Tφ reads as k g(x) = skx for all x ∈ ℤ.
    Thus, for g ≠ x ↦ sx, we have k = 0, and the equation φ(C) = T(C) reads as sC = 0 → C + 0.
    For g = x ↦ sx, any choice of C works.

  Implementation note:
    We first need to give a ring isomorphism between End(ℤ).
-/
def fn_eq_int (g : ℤ → ℤ) (s : ℤ) (f : ℤ → ℤ) := ∀ x y : ℤ, f (g x) + s * f y = f (f (x + y))



open function

namespace extra

lemma coe_End_int_of_int_eq_left_mul (x y : ℤ) : (x : add_monoid.End ℤ) y = x * y :=
  by rw ← int.smul_one_eq_coe; refl

/-- The ring isomorphism from ℤ to End(ℤ) -/
def End_int_of_int : ℤ ≃+* add_monoid.End ℤ :=
{ inv_fun := λ φ, φ (1 : ℤ),
  left_inv := λ x, by simp; rw [coe_End_int_of_int_eq_left_mul, mul_one],
  right_inv := λ φ, by ext; simp; rw [coe_End_int_of_int_eq_left_mul, mul_one],
  .. int.cast_ring_hom (add_monoid.End ℤ) }

lemma End_int_of_int_eq_mul (x y : ℤ) : End_int_of_int x y = x * y :=
begin
  simp [End_int_of_int, int.cast_ring_hom],
  exact coe_End_int_of_int_eq_left_mul x y
end

lemma End_int_eq_of_int_map_one (φ : ℤ →+ ℤ) : End_int_of_int (φ 1) = φ :=
  by change φ 1 with End_int_of_int.symm φ; rw ring_equiv.apply_symm_apply

lemma End_int_eq_map_one_mul (φ : ℤ →+ ℤ) (x : ℤ) : φ x = φ 1 * x :=
  by nth_rewrite 0 ← End_int_eq_of_int_map_one φ; rw End_int_of_int_eq_mul

lemma End_int_inj_of_ne_zero {x : ℤ} (h : x ≠ 0) : injective (End_int_of_int x) :=
begin
  intros a b h0,
  rwa [End_int_of_int_eq_mul, End_int_of_int_eq_mul, mul_right_inj' h] at h0
end

lemma End_int_eq_iff_eq_at_one (φ ρ : ℤ →+ ℤ) : φ = ρ ↔ φ 1 = ρ 1 :=
begin
  split,
  intros h; rw h,
  intros h; rw [← End_int_eq_of_int_map_one φ, h, End_int_eq_of_int_map_one ρ]
end



/-- Connection between fn_eq_int and fn_eq -/
lemma feq_int_iff_feq_gen (g : ℤ → ℤ) (s : ℤ) (f : ℤ → ℤ) :
    fn_eq_int g s f ↔ fn_eq g (extra.End_int_of_int s) f :=
  by simp only [fn_eq_int, fn_eq, extra.End_int_of_int_eq_mul]

end extra



/-- Final solution, case g ≠ x ↦ sx -/
theorem final_solution_int {g : ℤ → ℤ} (g_zero : g 0 = 0) {s : ℤ} (s_ne_zero : s ≠ 0) 
    (h : g ≠ λ x, s * x) (f : ℤ → ℤ) :
  fn_eq_int g s f ↔ f = 0 :=
begin
  symmetry; split,
  rintros rfl x y; simp only [pi.zero_apply, mul_zero, add_zero],
  intros h0,
  rw [extra.feq_int_iff_feq_gen, final_solution_general g_zero] at h0,
  work_on_goal 2 { exact extra.End_int_inj_of_ne_zero s_ne_zero },
  rcases h0 with ⟨φ, C, rfl, h0, h1, h2⟩,
  rw [extra.End_int_eq_iff_eq_at_one, add_monoid.coe_mul, comp_app,
      extra.End_int_of_int_eq_mul, pow_two, add_monoid.coe_mul, comp_app,
      extra.End_int_eq_map_one_mul, mul_eq_mul_right_iff] at h1,
  cases h1 with h1 h1,
  ---- φ(1) = s; a contradiction
  { exfalso; apply h; ext n,
    have h3 : (φ ∘ g) n = (extra.End_int_of_int s * φ) n := by rw h0,
    rw [comp_app, add_monoid.coe_mul, comp_app, extra.End_int_of_int_eq_mul,
        extra.End_int_eq_map_one_mul, extra.End_int_eq_map_one_mul φ n, h1] at h3,
    exact mul_left_cancel₀ s_ne_zero h3 },
  ---- φ(1) = 0; then f = 0
  { rw [extra.End_int_of_int_eq_mul, extra.End_int_eq_map_one_mul,
        h1, zero_mul, zero_eq_mul, or_iff_right s_ne_zero] at h2,
    rw [h2, pi.const_zero, add_zero, ← extra.End_int_eq_of_int_map_one φ, h1, map_zero],
    refl }
end

/-- Final solution, case g = x ↦ sx -/
theorem final_solution_int_case_r_eq_s {s : ℤ} (s_ne_zero : s ≠ 0) (f : ℤ → ℤ) :
  fn_eq_int (λ x, s * x) s f ↔ (f = 0 ∨ ∃ C : ℤ, f = λ x, s * x + C) :=
begin
  rw [extra.feq_int_iff_feq_gen, final_solution_general],
  work_on_goal 2 { rw mul_zero },
  work_on_goal 2 { exact extra.End_int_inj_of_ne_zero s_ne_zero },
  split,
  { rintros ⟨φ, C, rfl, junk, h, h0⟩; clear junk,
    rw extra.End_int_of_int_eq_mul at h0,
    rw [extra.End_int_eq_iff_eq_at_one, add_monoid.coe_mul, comp_app,
        extra.End_int_of_int_eq_mul, pow_two, add_monoid.coe_mul, comp_app,
        extra.End_int_eq_map_one_mul, mul_eq_mul_right_iff] at h,
    cases h with h h,
    right; use C; ext; rw [pi.add_apply, const_apply, extra.End_int_eq_map_one_mul, h],
    left,
    rw [extra.End_int_eq_map_one_mul, h, zero_mul, zero_eq_mul, or_iff_right s_ne_zero] at h0,
    rw [h0, pi.const_zero, add_zero, ← extra.End_int_eq_of_int_map_one φ, h, map_zero],
    refl },
  { rintros (rfl | ⟨C, rfl⟩),
    use [0, 0]; simp,
    rw [extra.End_int_of_int_eq_mul, mul_zero],
    work_on_goal 1 { repeat { split }},
    use [extra.End_int_of_int s, C]; repeat { split },
    ext; rw [pi.add_apply, const_apply, add_left_inj, extra.End_int_of_int_eq_mul],
    ext; rw [add_monoid.coe_mul, comp_apply, comp_apply, extra.End_int_of_int_eq_mul s x] }
end

/-- Final solution, original case: g = x ↦ 2x, s = 2 -/
theorem final_solution_original (f : ℤ → ℤ) :
    fn_eq_int (λ x, 2 * x) 2 f ↔ (f = 0 ∨ ∃ C : ℤ, f = λ x, 2 * x + C) :=
  final_solution_int_case_r_eq_s two_ne_zero f

end IMO2019A1
end IMOSL
