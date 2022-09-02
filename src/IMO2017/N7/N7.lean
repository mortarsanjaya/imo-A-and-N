import ring_theory.polynomial.homogeneous ring_theory.coprime.basic data.mv_polynomial.comm_ring

/-! # IMO 2017 N7 (P6) -/

namespace IMOSL
namespace IMO2017N7

open mv_polynomial finset



section extra

private lemma int_is_coprime_mul_eq {a b c d : ℤ}
  (h : is_coprime a c) (h0 : is_coprime b d) (h1 : a * d = b * c) :
  (a = b ∧ c = d) ∨ (a = -b ∧ c = -d) :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { rw [zero_mul, zero_eq_mul, or_comm] at h1,
    rcases h with ⟨u, v, h⟩,
    rcases h1 with rfl | rfl,
    rw [← add_mul, mul_zero] at h,
    exfalso; exact zero_ne_one h,
    rcases h0 with ⟨s, t, h0⟩,
    rw [mul_zero, zero_add] at h h0,
    replace h : c ∣ 1 := ⟨v, by rw [mul_comm, h]⟩,
    replace h0 : d ∣ 1 := ⟨t, by rw [mul_comm, h0]⟩,
    rw [← is_unit_iff_dvd_one, int.is_unit_iff] at h h0,
    rcases h with rfl | rfl; rcases h0 with rfl | rfl; norm_num },
  { have h2 : a.nat_abs = b.nat_abs :=
    begin
      apply nat.dvd_antisymm; rw int.nat_abs_dvd_iff_dvd,
      exact is_coprime.dvd_of_dvd_mul_right h ⟨d, h1.symm⟩,
      exact is_coprime.dvd_of_dvd_mul_right h0 ⟨c, h1⟩
    end,
    rw int.nat_abs_eq_nat_abs_iff at h2,
    rcases h2 with rfl | rfl,
    left; refine ⟨rfl, _⟩,
    rwa [eq_comm, mul_right_inj' ha] at h1,
    right; refine ⟨rfl, _⟩,
    rw neg_ne_zero at ha,
    rwa [neg_mul_comm, eq_comm, mul_right_inj' ha] at h1 }
end

private lemma homogeneous_smul_eval {σ R : Type*} [comm_ring R]
  (f : σ → R) (r : R) {φ : mv_polynomial σ R} {n : ℕ} (h : φ.is_homogeneous n) :
  eval (r • f) φ = r ^ n * eval f φ :=
begin
  rw [eval_eq, eval_eq, mul_sum],
  refine finset.sum_congr rfl (λ d hd, _),
  simp only [smul_eq_mul, pi.smul_apply, mul_pow],
  rw [mul_left_comm, prod_mul_distrib, prod_pow_eq_pow_sum]; congr,
  exact h (mem_support_iff.mp hd)
end



private noncomputable def CCX (u v : ℤ) : mv_polynomial bool ℤ := C u * X tt + C v * X ff

private lemma CCX_is_homogeneous_one (u v : ℤ) : (CCX u v).is_homogeneous 1 :=
begin
  refine is_homogeneous.add _ _; rw ← zero_add 1,
  all_goals { exact is_homogeneous.mul (is_homogeneous_C bool _) (is_homogeneous_X ℤ _) }
end

private lemma CCX_eval (u v : ℤ) (c : bool → ℤ) : eval c (CCX u v) = u * c tt + v * c ff :=
  by simp only [CCX, map_add, map_mul, eval_C, eval_X]

end extra







variables (xy : finset (bool → ℤ)) (h : ∀ p : bool → ℤ, p ∈ xy → is_coprime (p tt) (p ff))
include h

private lemma lem1 {c : bool → ℤ} (h0 : is_coprime (c tt) (c ff))
  (h1 : ∀ p : bool → ℤ, p ∈ xy → (c ≠ p ∧ c ≠ -p)) : ∃ φ : mv_polynomial bool ℤ,
  is_homogeneous φ xy.card ∧ (∀ p : bool → ℤ, p ∈ xy → eval p φ = 0) ∧ eval c φ ≠ 0 :=
begin
  refine ⟨xy.prod (λ p, CCX (p ff) (-p tt)), _, λ p h2, _, _⟩,
  { convert is_homogeneous.prod xy _ (λ _, 1) (λ i _, _),
    rw [sum_const, smul_eq_mul, mul_one],
    exact CCX_is_homogeneous_one _ _ },
  { rw [eval_prod, prod_eq_zero_iff],
    refine ⟨p, h2, _⟩,
    rw [CCX_eval, neg_mul, ← sub_eq_add_neg, mul_comm, sub_self] },
  { rw [eval_prod, prod_ne_zero_iff],
    rintros p h2 h3,
    rw [CCX_eval, neg_mul, ← sub_eq_add_neg, sub_eq_zero, mul_comm] at h3,
    rcases int_is_coprime_mul_eq h0 (h p h2) h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩,
    refine (h1 p h2).1 _; ext b; cases b; assumption,
    refine (h1 p h2).2 _; ext b; cases b; assumption }
end



/-- Final solution -/
theorem final_solution : ∃ (φ : mv_polynomial bool ℤ) (d : ℕ),
  0 < d ∧ is_homogeneous φ d ∧ ∀ p : bool → ℤ, p ∈ xy → mv_polynomial.eval p φ = 1 :=
begin
  -- First we solve the case xy = ∅ and the inductive base case |xy| = 1.
  induction xy using finset.induction_on with c xy hcxy xy_ih,
  exact ⟨0, 1, one_pos, is_homogeneous_zero bool ℤ 1, λ p h0, by exfalso; exact h0⟩,
  rcases xy.eq_empty_or_nonempty with rfl | hxy,
  rcases h c (mem_insert_self c ∅) with ⟨u, v, h0⟩,
  refine ⟨CCX u v, 1, one_pos, CCX_is_homogeneous_one _ _, λ p h1, _⟩,
  rw [mem_insert, or_iff_left (not_mem_empty p)] at h1,
  rw [CCX_eval, h1, h0],
  
  -- Now we focus on the induction step.
  -- But first separate the case where (x_n, y_n) = ± (x_i, y_i) for some i < n.
  simp only [mem_insert, forall_eq_or_imp] at h,
  cases h with hc_cop hxy_cop,
  replace xy_ih := xy_ih hxy_cop,
  rcases xy_ih with ⟨φ, d, hd0, hd1, h0⟩,
  by_cases h1 : ∃ p : bool → ℤ, p ∈ xy ∧ (c = p ∨ c = -p),
  rcases h1 with ⟨p, h1, rfl | rfl⟩,
  exfalso; exact hcxy h1,
  refine ⟨φ ^ 2, 2 * d, mul_pos two_pos hd0, _, λ q h2, _⟩,
  rw [sq, two_mul]; exact is_homogeneous.mul hd1 hd1,
  rw [mem_insert, or_comm] at h2; rcases h2 with h2 | rfl,
  rw [map_pow, h0 q h2, one_pow],
  rw [map_pow, ← neg_one_smul ℤ p, homogeneous_smul_eval p _ hd1, h0 p h1,
      mul_one, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow],

  -- This is the main case we work with.
  simp only [not_exists, not_or_distrib, not_and] at h1,
  replace h1 := lem1 xy hxy_cop hc_cop h1,
  rcases h1 with ⟨ρ, hρ, hρxy, hρc⟩,
  sorry
end

end IMO2017N7
end IMOSL
