import
  IMO2020.N5.N5_extra.good_map
  IMO2020.N5.N5_extra.strong_map.characterization
  field_theory.finite.basic

/-! # IMO 2020 N5, Weak Generalized Version -/

namespace IMOSL
namespace IMO2020N5

open additive_map
open_locale classical



variables {M : Type*} [add_cancel_comm_monoid M] [no_zero_smul_divisors ℕ M]



private lemma lem1 {f : additive_map M} {p : ℕ} (h : p.prime) (h0 : good p f)
  {k : ℕ} (h1 : k < p) : f k = 0 :=
begin
  rcases k.eq_zero_or_pos with rfl | h2,
  rw map_zero f,
  have h3 := nat.not_dvd_of_pos_of_lt h2 h1,
  have h4 := good_prime_pow_mod_p f h h0 (nat.not_dvd_of_pos_of_lt h2 h1) p.totient,
  rw [← h.coprime_iff_not_dvd, nat.coprime_comm] at h3,
  replace h3 := nat.modeq.pow_totient h3,
  rw [nat.modeq, nat.mod_eq_of_lt h.one_lt] at h3,
  rw [h3, map_one_zero, nat.mod_eq_of_lt h1, eq_comm, smul_eq_zero, or_comm] at h4,
  cases h4 with h4 h4,
  exact h4,
  exfalso; exact ne_of_gt (nat.totient_pos h.pos) h4
end

private lemma lem2 {f : additive_map M} (h : wide f) : f = 0 :=
begin
  ext k,
  obtain ⟨p, ⟨h0, h1⟩, h2⟩ := set.infinite.exists_nat_lt h k,
  rw zero_apply; exact lem1 h0 h1 h2
end

instance pcompl_hom_unique {p : ℕ} [fact (0 < p)] : unique (pcompl_hom M p) :=
{ default := 0,
  uniq := λ f, begin
    ext k; rw pcompl_hom.zero_apply,
    have h := congr_arg f (zmod.pow_totient k),
    rw [pcompl_hom.map_one, pcompl_hom.map_pow_smul, smul_eq_zero, or_comm] at h,
    cases h with h h,
    exact h,
    exfalso; exact ne_of_gt (nat.totient_pos (fact.out (0 < p))) h
  end }

private lemma lem3 (f : additive_map M) (p : ℕ) [fact p.prime] :
  strong p f ↔ ∃ c : M, ⇑f = λ n, padic_val_nat p n • c :=
begin
  rw pstrong_iff,
  simp only [unique.exists_iff, default, pcompl_hom.zero_apply, add_zero],
  conv_rhs { congr, funext, rw function.funext_iff }
end



/-- Final solution -/
theorem final_solution (f : additive_map M) : {p : ℕ | good p f}.infinite ↔
  f = 0 ∨ ∃ (p : ℕ) (h : p.prime) (c : M), c ≠ 0 ∧ ⇑f = λ n, padic_val_nat p n • c :=
begin
  rw good_infinite_iff_wide_or_strong; split,
  { rintros (h | ⟨p, hp, h⟩),
    left; exact lem2 h,
    haveI : fact p.prime := ⟨hp⟩,
    rw lem3 at h; cases h with c h,
    rcases ne_or_eq c 0 with hc | rfl,
    right; exact ⟨p, hp, c, hc, h⟩,
    left; ext; simp only [h, smul_zero, zero_apply] },
  { rintros (rfl | ⟨p, hp, c, hc, h⟩),
    right; refine ⟨2, nat.prime_two, _⟩,
    rintros k a b - - -; rw [zero_apply, zero_apply],
    right; use [p, hp],
    haveI : fact p.prime := ⟨hp⟩,
    rw lem3; use c; exact h }
end

end IMO2020N5
end IMOSL
