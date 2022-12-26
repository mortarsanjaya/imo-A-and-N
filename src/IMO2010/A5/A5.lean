import algebra.module.basic group_theory.torsion extra.number_theory.pos_rat_primes

/-! # IMO 2010 A5 -/

namespace IMOSL
namespace IMO2010A5

def good' {G : Type*} [add_monoid G] (f : G → G) :=
  ∀ x y : G, f (2 • f x + y) = 3 • x + f (x + y)

def good {G : Type*} [monoid G] (f : G → G) :=
  ∀ x y : G, f (f x ^ 2 * y) = x ^ 3 * f (x * y)



private theorem correspondence {G : Type*} [monoid G] (f : G → G) :
  good f ↔ good' (λ x : additive G, f x) := by refl

private lemma neg_is_good' {G : Type*} [add_comm_group G] : good' (has_neg.neg : G → G) :=
  λ x y, by rw [eq_add_neg_iff_add_eq, add_comm, ← sub_eq_add_neg,
    add_sub_add_right_eq_sub, smul_neg, sub_neg_eq_add, eq_comm, succ_nsmul]

private lemma good'_iff {G : Type*} [add_comm_group G] [no_zero_smul_divisors ℕ G] :
  ∀ f : G → G, good' f ↔ ∃ φ : G →+ G, f = φ ∧ ∀ x : G, 2 • φ (φ x) = 3 • x + φ x :=
begin
  ---- First, solve the `←` direction.
  intros f; symmetry; refine ⟨λ h x y, _, λ h, _⟩,
  rcases h with ⟨φ, rfl, h⟩; rw [map_add, map_add, ← add_assoc, ← h, map_nsmul],

  ---- Now solve the `→` direction
  -- First reduce to just `f` being additive.
  have h0 := λ x, h x 0,
  simp_rw add_zero at h0,
  suffices : ∀ x y, f (x + y) = f x + f y,
  { refine ⟨⟨f, _, this⟩, rfl, λ x, _⟩,
    replace this := this 0 0,
    rwa [add_zero, self_eq_add_left] at this,
    rw [add_monoid_hom.coe_mk, ← h0, two_nsmul, ← this, ← two_nsmul] },

  -- Reduce to showing that `f` is injective.
  revert h; suffices : function.injective f,
  { intros h x y,
    have h1 := h x (2 • f y),
    rw [← smul_add, add_comm x, h, ← add_assoc, ← smul_add, add_comm y, ← h0] at h1,
    replace h1 := this h1,
    rwa [smul_right_inj, eq_comm] at h1,
    exact two_ne_zero },

  -- Now show that `f` is injective.
  intros x y h,
  have h1 := h0 y,
  rwa [← h, h0, add_left_inj, smul_right_inj] at h1,
  exact three_ne_zero
end







/-- Final solution, additive version -/
theorem final_solution_additive {G : Type*} [add_comm_group G]
  {S : Type*} {ρ : G →+ S → ℤ} (h : function.injective ρ) :
  ∀ f : G → G, good' f ↔ f = has_neg.neg :=
begin
  ---- A characterization of zeroes in `G` using `ρ`
  simp_rw [injective_iff_map_eq_zero', function.funext_iff, pi.zero_apply] at h,

  ---- Set up `no_zero_smul_divisors ℕ G` instance
  haveI _inst_2 : no_zero_smul_divisors ℕ G :=
  ⟨λ n x h1, begin
      rw [← h, or_iff_not_imp_left]; intros h2 s,
      rw ← h at h1; replace h1 := h1 s,
      rwa [map_nsmul, pi.smul_apply, smul_eq_zero, or_iff_right h2] at h1
  end⟩,

  ---- Setup for the final step of induction
  refine λ f, ⟨λ h0, _, λ h0, by subst h0; exact neg_is_good'⟩,
  rw good'_iff at h0; rcases h0 with ⟨φ, rfl, h0⟩,
  obtain ⟨γ, rfl⟩ : ∃ γ : G →+ G, γ - add_monoid_hom.id G = φ :=
    ⟨φ + add_monoid_hom.id G, add_sub_cancel _ _⟩,
  simp_rw [add_monoid_hom.sub_apply, add_monoid_hom.id_apply, map_sub, nsmul_sub] at h0,
  replace h0 : ∀ x : G, 2 • γ (γ x) - 5 • γ x = 0 :=
    λ x, by replace h0 := h0 x; rwa [succ_nsmul' x 2, add_add_sub_cancel, add_comm, ← sub_add,
      add_left_inj, sub_sub, ← add_nsmul, sub_eq_iff_eq_add, ← succ_nsmul, ← sub_eq_zero] at h0,
  simp_rw [← h, map_sub, pi.sub_apply, sub_eq_zero, map_nsmul, pi.smul_apply,
    nsmul_eq_mul, nat.cast_bit1, nat.cast_bit0, nat.cast_one] at h0,
  simp_rw [function.funext_iff, add_monoid_hom.sub_apply,
    add_monoid_hom.id_apply, sub_eq_neg_self, ← h],
  clear h; intros x s; revert x,
  suffices : ∀ (k : ℕ) (x : G), 2 ^ k ∣ ρ (γ x) s,
  { intros x; refine int.eq_zero_of_abs_lt_dvd (this (ρ (γ x) s).nat_abs x) _,
    change |↑(ρ (γ x) s)| < ((2 : ℕ) : ℤ) ^ (ρ (γ x) s).nat_abs,
    rw [← nat.cast_pow, ← int.cast_nat_abs, nat.cast_lt],
    exact (ρ (γ x) s).nat_abs.lt_two_pow },

  ---- Induction
  intros k; induction k with k h; intros x,
  rw pow_zero; exact one_dvd _,
  replace h := h (γ x); cases h with c h,
  replace h0 := h0 x s,
  generalize_hyp : ρ (γ (γ x)) s = A at h h0,
  subst h; generalize_hyp : ρ (γ x) s = A at h0 ⊢,
  rw [← mul_assoc, ← pow_succ] at h0,
  refine (is_coprime.pow_left ⟨(-2 : ℤ), 1, _⟩).dvd_of_dvd_mul_left ⟨c, h0.symm⟩,
  norm_num
end



/-- Final solution, multiplicative version -/
theorem final_solution_multiplicative {G : Type*} [comm_group G]
  {S : Type*} {ρ : additive G →+ S → ℤ} (h : function.injective ρ) :
  ∀ f : G → G, good f ↔ f = has_inv.inv :=
  final_solution_additive h



/-- Final solution, original (`ℚ+`) version -/
theorem final_solution_original :
  ∀ f : {q : ℚ // 0 < q} → {q : ℚ // 0 < q}, good f ↔ f = has_inv.inv :=
  final_solution_multiplicative extra.pos_rat_factor_hom.inj

end IMO2010A5
end IMOSL
