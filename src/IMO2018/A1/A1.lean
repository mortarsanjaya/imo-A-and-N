import extra.number_theory.pos_rat_primes

/-! # IMO 2018 A1 -/

namespace IMOSL
namespace IMO2018A1

def good' (n : ℤ) {G : Type*} [add_group G] (f : G → G) :=
  ∀ x y : G, f (n • (x + f y)) = n • f x + f y

def good (n : ℤ) {G : Type*} [group G] (f : G → G) :=
  ∀ x y : G, f ((x * f y) ^ n) = f x ^ n * f y



/-- Final solution, additive version -/
theorem final_solution_additive {n : ℤ} (h : 1 < |n|) {G : Type*} [add_group G]
  {S : Type*} {ρ : G →+ S → ℤ} (h0 : function.injective ρ) :
  ∀ f : G → G, good' n f ↔ f = 0 :=
begin
  ---- First, remove the `←` direction
  intros f; symmetry; refine ⟨λ h1 x y, _, λ h1, _⟩,
  subst h1; simp_rw [pi.zero_apply, smul_zero, add_zero],

  ---- Initial setup
  simp_rw [injective_iff_map_eq_zero', function.funext_iff, pi.zero_apply] at h0,
  simp_rw [function.funext_iff, pi.zero_apply, ← h0],
  haveI _inst_2 : no_zero_smul_divisors ℤ G :=
  ⟨λ k x h2, begin
      rw [← h0, or_iff_not_imp_left]; intros h3 s,
      rw ← h0 at h2; replace h2 := h2 s,
      rwa [map_zsmul, pi.smul_apply, smul_eq_zero, or_iff_right h3] at h2
  end⟩,

  ---- Some more setup
  replace h0 := h1 (-f 0) 0,
  rw [neg_add_self, smul_zero, self_eq_add_left, smul_eq_zero,
      or_iff_right (abs_pos.mp (lt_trans one_pos h : 0 < |n|))] at h0,
  have h2 := λ x, h1 x (-f 0),
  simp_rw [h0, add_zero] at h2,
  replace h1 := h1 0,
  simp_rw [zero_add, h2] at h1,
  replace h0 := h2 0,
  replace h2 : n ≠ 1 := by rintros rfl; rw abs_one at h; exact ne_of_gt h rfl,
  rw [← one_zsmul (f (n • 0)), smul_zero, eq_comm, ← add_neg_eq_zero,
      ← sub_zsmul, smul_eq_zero, sub_eq_zero, or_iff_right h2] at h0,
  simp_rw [h0, smul_zero, zero_add] at h1,
  clear h0 h2,

  suffices : ∀ (s : S) (k : ℕ) (x : G), |n| ^ k ∣ ρ (f x) s,
  { intros x s; refine int.eq_zero_of_abs_lt_dvd (this s (ρ (f x) s).nat_abs x) _,
    lift |n| to ℕ using abs_nonneg n with N,
    rw nat.one_lt_cast at h,
    change |↑(ρ (f x) s)| < (N : ℤ) ^ (ρ (f x) s).nat_abs,
    rw [← nat.cast_pow, ← int.cast_nat_abs, nat.cast_lt],
    exact nat.lt_pow_self h (ρ (f x) s).nat_abs },

  ---- Induction step
  simp_rw [← abs_pow, abs_dvd],
  intros s k; induction k with k h0; intros x,
  rw pow_zero; exact one_dvd (ρ (f x) s),
  rw [← h1, map_zsmul, pi.smul_apply, smul_eq_mul, pow_succ],
  exact mul_dvd_mul_left n (h0 (f x))
end



/-- Final solution, multiplicative version -/
theorem final_solution_multiplicative {n : ℤ} (h : 1 < |n|) {G : Type*} [group G]
  {S : Type*} {ρ : additive G →+ S → ℤ} (h0 : function.injective ρ) :
  ∀ f : G → G, good n f ↔ f = 1 :=
  final_solution_additive h h0



/-- Final solution, `ℚ+` version -/
theorem final_solution_rat {n : ℤ} (h : 1 < |n|) :
  ∀ f : {q : ℚ // 0 < q} → {q : ℚ // 0 < q}, good n f ↔ f = λ _, 1 :=
  final_solution_multiplicative h extra.pos_rat_factor_hom.inj

end IMO2018A1
end IMOSL
