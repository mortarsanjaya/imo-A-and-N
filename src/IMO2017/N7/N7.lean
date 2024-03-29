import
  ring_theory.mv_polynomial.homogeneous
  ring_theory.coprime.basic
  data.mv_polynomial.comm_ring
  data.nat.totient
  field_theory.finite.basic
  data.zmod.basic

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

private lemma int_exists_pow_modeq_one_of_coprime {a b : ℤ} (h : is_coprime a b) :
  ∃ K : ℕ, 0 < K ∧ a ^ K ≡ 1 [ZMOD b] :=
begin
  rcases eq_or_ne b 0 with rfl | h0,
  rw is_coprime_zero_right at h; exact ⟨2, two_pos, by rw int.is_unit_sq h⟩,
  replace h0 := int.nat_abs_pos_of_ne_zero h0,
  refine ⟨b.nat_abs.totient, nat.totient_pos h0, int.modeq.symm _⟩,
  rw [int.modeq_iff_dvd, ← int.nat_abs_dvd],
  rw int.coprime_iff_nat_coprime at h,
  generalize_hyp : b.nat_abs = n at h h0 ⊢; clear b,
  rw [← nat.succ_le_iff, le_iff_eq_or_lt] at h0,
  rcases h0 with rfl | h0,
  rw nat.cast_one; exact one_dvd _,
  rw [← nat.succ_le_iff, le_iff_eq_or_lt] at h0,
  rcases h0 with rfl | h0,
  { rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd nat.prime_two] at h,
    rw [nat.cast_succ, nat.cast_one, nat.totient_two, pow_one, ← bit0],
    apply int.dvd_sub_of_mod_eq,
    rwa [← int.not_even_iff, ← int.nat_abs_even, nat.even_iff, ← nat.dvd_iff_mod_eq_zero] },
  replace h := nat.modeq.pow_totient h,
  obtain ⟨c, h1⟩ := nat.totient_even h0,
  rw [h1, ← two_mul] at h ⊢,
  rw [pow_mul, ← int.nat_abs_sq, ← pow_mul, ← nat.cast_pow],
  change (1 : ℤ) with ((1 : ℕ) : ℤ),
  rw [← int.modeq_iff_dvd, int.coe_nat_modeq_iff],
  exact nat.modeq.symm h
end

private lemma int_coprime_iff_not_exists_prime_dvd (a b : ℤ) :
  is_coprime a b ↔ ∀ p : ℕ, p.prime → ¬((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b) :=
begin
  conv_rhs { find (¬_) { rw [← int.nat_abs_dvd_iff_dvd, int.nat_abs_of_nat,
    ← int.nat_abs_dvd_iff_dvd, int.nat_abs_of_nat, ← nat.dvd_gcd_iff] } },
  rw [← nat.eq_one_iff_not_exists_prime_dvd, int.coprime_iff_nat_coprime]
end



section is_homogeneous

variables {σ R : Type*} [comm_ring R]

private lemma homogeneous_smul_eval (f : σ → R) (r : R) {φ : mv_polynomial σ R}
  {n : ℕ} (h : φ.is_homogeneous n) : eval (r • f) φ = r ^ n * eval f φ :=
begin
  rw [eval_eq, eval_eq, mul_sum],
  refine finset.sum_congr rfl (λ d hd, _),
  simp only [smul_eq_mul, pi.smul_apply, mul_pow],
  rw [mul_left_comm, prod_mul_distrib, prod_pow_eq_pow_sum]; congr,
  exact h (mem_support_iff.mp hd)
end

private lemma homogeneous_smul_eval₂ {S : Type*} [comm_ring S] (ρ : R →+* S)
  (f : σ → S) (r : S) {φ : mv_polynomial σ R} {n : ℕ} (h : φ.is_homogeneous n) :
  eval₂ ρ (r • f) φ = r ^ n * eval₂ ρ f φ :=
begin
  rw [eval₂_eq, eval₂_eq, mul_sum],
  refine finset.sum_congr rfl (λ d hd, _),
  simp only [smul_eq_mul, pi.smul_apply, mul_pow],
  rw [mul_left_comm, prod_mul_distrib, prod_pow_eq_pow_sum]; congr,
  exact h (mem_support_iff.mp hd)
end

private lemma homogeneous_pow (k : ℕ) {φ : mv_polynomial σ R} {n : ℕ} (h : φ.is_homogeneous n) :
  (φ ^ k).is_homogeneous (k * n) :=
begin
  induction k with k k_ih,
  rw [pow_zero, zero_mul]; exact is_homogeneous_one σ R,
  rw [pow_succ', nat.succ_mul]; exact is_homogeneous.mul k_ih h
end

end is_homogeneous



section CCX

section comm_ring

variables {R : Type*} [comm_ring R]

private noncomputable def CCX (u v : R) : mv_polynomial bool R := C u * X tt + C v * X ff

private lemma CCX_is_homogeneous_one (u v : R) : (CCX u v).is_homogeneous 1 :=
begin
  refine is_homogeneous.add _ _; rw ← zero_add 1,
  all_goals { exact is_homogeneous.mul (is_homogeneous_C bool _) (is_homogeneous_X R _) }
end

private lemma CCX_eval (u v : R) (c : bool → R) : eval c (CCX u v) = u * c tt + v * c ff :=
  by simp only [CCX, map_add, map_mul, eval_C, eval_X]

private lemma CCX_prod_is_homogeneous_card [decidable_eq R] (xy : finset (bool → R)) :
  (xy.prod (λ p, CCX (p ff) (-p tt))).is_homogeneous xy.card :=
begin
  induction xy using finset.induction_on with c xy h h0,
  rw [prod_empty, card_empty]; exact is_homogeneous_one bool R,
  rw [prod_insert h, card_insert_of_not_mem h, add_comm],
  exact is_homogeneous.mul (CCX_is_homogeneous_one _ _) h0
end

private lemma CCX_prod_eval_eq_zero_of_mem [decidable_eq R] [is_domain R]
  {xy : finset (bool → R)} {p : bool → R} (h : p ∈ xy) :
  eval p (xy.prod (λ p, CCX (p ff) (-p tt))) = 0 :=
begin
  rw [eval_prod, prod_eq_zero_iff],
  refine ⟨p, h, _⟩,
  rw [CCX_eval, neg_mul, mul_comm, add_neg_self]
end

end comm_ring



section field

variables {F : Type*} [field F]

private lemma CCX_eval_eq_zero_iff_exists_eq_smul (p : bool → F) (u v : F) :
  eval p (CCX u v) = 0 ↔ p = 0 ∨ ∃ α : F, u = α * p ff ∧ v = -α * p tt :=
begin
  rw [CCX_eval, add_eq_zero_iff_eq_neg, ← neg_mul],
  cases eq_or_ne (p tt) 0 with h h,
  { rw [h, mul_zero, zero_eq_mul],
    cases eq_or_ne (p ff) 0 with h0 h0,
    rw [h0, eq_self_iff_true, or_true, true_iff],
    left; ext b; cases b; assumption,
    rw [iff_false_intro h0, or_false, neg_eq_zero, or_iff_right],
    work_on_goal 2 { rintros rfl; exact h0 rfl },
    refine ⟨λ h1, ⟨u / p ff, (div_mul_cancel _ h0).symm, by rw [mul_zero, h1]⟩, λ h1, _⟩,
    rcases h1 with ⟨α, rfl, rfl⟩,
    rw mul_zero },
  { rw or_iff_right,
    work_on_goal 2 { rintros rfl; exact h rfl },
    refine ⟨λ h1, ⟨-v / p tt, _, _⟩, λ h1, _⟩,
    rw [← mul_div_right_comm, ← h1, mul_div_cancel _ h],
    rw [neg_div, neg_neg, div_mul_cancel _ h],
    rcases h1 with ⟨α, rfl, rfl⟩,
    rw [neg_mul α, neg_neg, mul_right_comm] }
end

end field

end CCX



section zmod

private lemma CCX_eval_zmod_cast (p : ℕ) (u v : ℤ) (c : bool → ℤ) :
  (eval c (CCX u v) : zmod p) = eval (coe ∘ c) (CCX (u : zmod p) v) :=
  by simp only [CCX_eval, function.comp_app, int.cast_add, int.cast_mul]

end zmod

end extra



/-- Final solution -/
theorem final_solution {xy : finset (bool → ℤ)}
  (h : ∀ p : bool → ℤ, p ∈ xy → is_coprime (p tt) (p ff)) :
  ∃ (φ : mv_polynomial bool ℤ) (d : ℕ),
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
  rw ← card_pos at hxy,

  /-
  Now we focus on the induction step.
  Set ρ = ∏ [p ∈ xy] (λ p, p_f X - p_t Y). 
  The desired polynomial is φ^K + Mρ (uc_t + vc_f)^L for some K L : ℕ and M : ℤ.
  The sufficient properties for its construction is Kd = |xy| + L and ρ(c) ∣ φ(c)^K - 1.
  Simplifying, it suffices to prove that there exists K such that |xy| ≤ Kd and ρ(c) ∣ φ(c)^K - 1.
  -/
  simp only [mem_insert, forall_eq_or_imp] at h,
  cases h with hc_cop hxy_cop,
  replace xy_ih := xy_ih hxy_cop,
  rcases xy_ih with ⟨φ, d, hd0, hd1, h0⟩,
  let ρ := xy.prod (λ p, CCX (p ff) (-p tt)),
  suffices : ∃ K : ℕ, xy.card ≤ K * d ∧ eval c ρ ∣ (eval c φ) ^ K - 1,
  { rcases this with ⟨K, h1, M, h2⟩,
    rcases hc_cop with ⟨u, v, hc_cop⟩,
    rw le_iff_exists_add at h1; cases h1 with L h1,
    refine ⟨φ ^ K + C (-M) * ρ * (CCX u v) ^ L, xy.card + L, _, is_homogeneous.add _ _, λ p hp, _⟩,
    exact lt_of_lt_of_le hxy (self_le_add_right _ _),
    rw ← h1; exact homogeneous_pow K hd1,
    { rw ← nat.zero_add xy.card,
      refine is_homogeneous.mul (is_homogeneous.mul (is_homogeneous_C bool (-M)) _) _,
      exact CCX_prod_is_homogeneous_card xy,
      convert homogeneous_pow L (CCX_is_homogeneous_one u v); rw mul_one },
    { simp only [map_add, map_mul, map_pow, C_neg, map_neg, neg_mul, eval_C],
      rw mem_insert at hp; rcases hp with rfl | h3,
      rw [CCX_eval, hc_cop, one_pow, mul_one, mul_comm, ← h2, neg_sub, add_comm, sub_add_cancel],
      rw [h0 p h3, one_pow, CCX_prod_eval_eq_zero_of_mem h3,
          mul_zero, zero_mul, neg_zero, add_zero] } },

  -- One can reduce one step further: only need to show that φ(c) and ρ(c) are coprime.
  suffices : is_coprime (eval c φ) (eval c ρ),
  { rcases int_exists_pow_modeq_one_of_coprime this with ⟨K, h1, h2⟩,
    refine ⟨xy.card * K, _, _⟩,
    rw mul_assoc; exact nat.le_mul_of_pos_right (mul_pos h1 hd0),
    rw [mul_comm, pow_mul, ← int.modeq_iff_dvd],
    convert int.modeq.symm (int.modeq.pow xy.card h2); rw one_pow },

  -- Next, reduce to coprimality with respect to each p ∈ xy, then chore.
  rw eval_prod; refine is_coprime.prod_right (λ p hp, _),
  replace h0 := h0 p hp,
  replace hxy_cop := hxy_cop p hp,
  clear hcxy hxy ρ hp hd0 xy,

  -- Now prove the coprimality result.
  rw int_coprime_iff_not_exists_prime_dvd at hc_cop hxy_cop ⊢,
  intros q hq h1; replace hxy_cop := hxy_cop q hq; replace hc_cop := hc_cop q hq,
  repeat { rw ← zmod.int_coe_zmod_eq_zero_iff_dvd at hc_cop hxy_cop h1 },
  haveI : fact q.prime := ⟨hq⟩,
  cases h1 with h1 h2,
  rw [CCX_eval_zmod_cast, CCX_eval_eq_zero_iff_exists_eq_smul] at h2,
  rcases h2 with h2 | ⟨α, h2⟩,
  exact hc_cop ⟨congr_fun h2 tt, congr_fun h2 ff⟩,
  revert h0; suffices : (eval p φ : zmod q) = 0,
  { intros h0,
    rw [zmod.int_coe_zmod_eq_zero_iff_dvd, h0] at this,
    replace this := int.eq_one_of_dvd_one q.cast_nonneg this,
    rw nat.cast_eq_one at this,
    rw this at hq; exact nat.not_prime_one hq },
  clear hc_cop hxy_cop,
  rw [eval, ← int.coe_cast_ring_hom, map_eval₂_hom,
      coe_eval₂_hom, ring_hom_comp_triple.comp_eq] at h1 ⊢,
  replace h2 : (λ i, int.cast_ring_hom (zmod q) (p i))
    = α • (λ i, int.cast_ring_hom (zmod q) (c i)) :=
  begin
    cases h2 with h2 h3,
    rw [neg_mul, int.cast_neg, neg_inj] at h3,
    ext b; rw [eq_int_cast, pi.smul_apply, smul_eq_mul, eq_int_cast],
    cases b; assumption
  end,
  rw [h2, homogeneous_smul_eval₂ _ _ _ hd1, h1, mul_zero]
end

end IMO2017N7
end IMOSL
