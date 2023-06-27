import
  IMO2020.N5.regular_map
  IMO2020.N5.legendre_stack_map
  extra.number_theory.divisor_closed_prop

/-! # IMO 2020 N5, Generalized Version -/

namespace IMOSL
namespace IMO2020N5

open additive_map extra additive
open_locale classical



def good {α : Type*} (f : ℕ → α) (n : ℕ) := ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → a + b = n → f a = f b



section extra_lemmas

lemma padic_add_eq_p_pow (p : ℕ) [fact (p.prime)] {a b k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : a + b = p ^ k) : padic_val_nat p a = padic_val_nat p b :=
begin
  revert a b k ha hb h,
  suffices : ∀ {a b k : ℕ}, a ≠ 0 → b ≠ 0 → a + b = p ^ k → padic_val_nat p a ≤ padic_val_nat p b,
    intros a b k ha hb h; exact le_antisymm (this ha hb h) (this hb ha (by rw [add_comm, h])),
  intros a b k ha hb h,
  suffices : ∀ n : ℕ, p ^ n ∣ a → p ^ n ∣ b,
  { replace this := this (padic_val_nat p a) pow_padic_val_nat_dvd,
    rwa [padic_val_nat_dvd_iff, or_iff_right hb] at this },
  intros n h0,
  rw [nat.dvd_add_iff_right h0, h, nat.pow_dvd_pow_iff_le_right (fact.out p.prime).one_lt],
  refine le_of_lt (lt_of_not_le (λ h1, _)),
  rw [← nat.pow_dvd_pow_iff_le_right (fact.out p.prime).one_lt, ← h] at h1,
  replace h0 := nat.le_of_dvd (zero_lt_iff.mpr ha) (dvd_trans h1 h0),
  rw [add_le_iff_nonpos_right, le_zero_iff] at h0,
  exact hb h0
end

end extra_lemmas







section infinite_good_iff

variables {M : Type*} [add_cancel_comm_monoid M] (f : additive_map M)

/-- `1` is always `f`-good. -/
private lemma good_one : good f 1 :=
begin
  rintros a b ha hb h,
  rw ← zero_lt_iff at ha hb,
  exfalso; refine ne_of_gt _ h,
  rw ← nat.succ_le_iff at ha hb ⊢,
  exact add_le_add ha hb
end

/-- `0` is always `f`-good. -/
private lemma good_zero : good f 0 :=
  λ a b ha hb h, by exfalso; exact ha (add_eq_zero_iff.mp h).left

/-- The `f`-good predicate is divisor-closed. -/
private lemma good_dc : divisor_closed (good f) :=
begin
  rintros n h h0 d ⟨c, rfl⟩,
  rcases eq_or_ne c 0 with rfl | hc,
  exfalso; exact h d.mul_zero,
  intros a b ha hb h1,
  replace h0 := h0 _ _ (mul_ne_zero ha hc) (mul_ne_zero hb hc) (by rw [← add_mul, h1]),
  rwa [map_mul f ha hc, map_mul f hb hc, add_left_inj] at h0
end

/-- The `f`-good predicate is infinite iff `f` is either `wide` or `p`-strong for some prime `p`. -/
theorem good_infinite_iff_wide_or_strong :
  (set_of (good f)).infinite ↔ wide (good f) ∨ ∃ p : ℕ, p.prime ∧ strong p (good f) :=
  dc_infinite_iff_wide_or_strong (good_dc f)

end infinite_good_iff







section good_prime_props

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} [fact p.prime] {f : additive_map M} (h : good f p)
include h

private theorem good_prime_mul_lt_p {k m : ℕ} (hk : k ≠ 0) (hkp : k < p) (hm : m ≠ 0) (hmp : m < p) :
  f (k * m % p) = f k + f m :=
begin
  have hp := fact.out p.prime,
  revert m hm hmp; induction k using nat.strong_induction_on with k k_ih; intros m hm hmp,
  induction m using nat.strong_induction_on with m m_ih,
  cases lt_or_le (k * m) p with h0 h0,
  rw [nat.mod_eq_of_lt h0, map_mul f hk hm],
  let c := p / m,
  let d := p % m,
  have X : ∀ a b : ℕ, b % a ≠ 0 ↔ ¬a ∣ b :=
    λ a b, by rw [ne.def, nat.dvd_iff_mod_eq_zero],

  have hd : d ≠ 0 :=
  begin
    rw X; intros h1,
    rw [← zero_lt_iff, ← nat.succ_le_iff, le_iff_eq_or_lt, eq_comm] at hm,
    rcases hm with rfl | hm,
    rw mul_one at h0; exact not_le_of_lt hkp h0,
    replace hm := nat.min_fac_le_of_dvd hm h1,
    rw nat.prime.min_fac_eq hp at hm; exact not_le_of_lt hmp hm
  end,
  rw ← zero_lt_iff at hm,
  replace m_ih : f (k * d % p) = f k + f d :=
    m_ih d (p.mod_lt hm) hd (lt_trans (p.mod_lt hm) hmp),
  have hc : c ≠ 0 :=
    by rw [ne.def, nat.div_eq_zero_iff hm]; exact lt_asymm hmp,
  replace h0 : c < k :=
  begin
    rw le_iff_lt_or_eq at h0,
    rcases h0 with h0 | h0,
    rwa nat.div_lt_iff_lt_mul hm,
    simp only [d, h0, nat.mul_mod_left, not_lt_zero'] at hd,
    exfalso; exact hd rfl
  end,
  replace k_ih := @k_ih c h0 hc (lt_trans h0 hkp),
  have h1 : c * m + d = p := nat.div_add_mod' p m,
  have h2 : ∀ n : ℕ, n ≠ 0 → n < p → ¬p ∣ n :=
    λ n hn0, nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr hn0),
  have hcp := lt_trans h0 hkp,
  have hdp := lt_trans (p.mod_lt hm) hmp,
  replace hkp := h2 k hk hkp,
  rw zero_lt_iff at hm,
  replace hmp := h2 m hm hmp,
  have hkcmp := hp.not_dvd_mul hkp (hp.not_dvd_mul (h2 c hc hcp) hmp),
  rw [← add_left_inj (f c), add_assoc, add_comm (f m), add_comm,
      ← map_mul f hc hm, h _ d (mul_ne_zero hc hm) hd h1,
      ← m_ih, ← k_ih (by rw X; exact hp.not_dvd_mul hkp hmp) (nat.mod_lt _ hp.pos),
      ← nat.mod_eq_of_lt hcp, ← nat.mul_mod, mul_left_comm],
  refine h _ _ _ _ _,
  rw X; exact hkcmp,
  rw X; refine hp.not_dvd_mul hkp (h2 d hd hdp),
  rw [← nat.add_mod_add_of_le_add_mod, ← mul_add, h1, nat.mul_mod_left, zero_add],
  refine nat.le_mod_add_mod_of_dvd_add_of_not_dvd _ hkcmp,
  rw [← mul_add, h1, mul_comm]; use k
end

/-- The above result, but given completely in modulo `p`. -/
private theorem good_prime_mul_mod_p {k m : ℕ} (hkp : ¬p ∣ k) (hmp : ¬p ∣ m) :
  f (k * m % p) = f (k % p) + f (m % p) :=
begin
  rw [nat.dvd_iff_mod_eq_zero, ← ne.def] at hkp hmp,
  have hp := fact.out p.prime,
  rw [← good_prime_mul_lt_p h hkp (k.mod_lt hp.pos) hmp (m.mod_lt hp.pos), ← nat.mul_mod]
end

/-- A corollary of `good_prime_mul_mod_p` with power in place of multiplication. -/
private theorem good_prime_pow_mod_p {k : ℕ} (hkp : ¬p ∣ k) (t : ℕ) :
  f (k ^ t % p) = t • f (k % p) :=
begin
  induction t with t t_ih,
  rw [zero_smul, pow_zero, nat.mod_eq_of_lt (fact.out p.prime).one_lt, additive_map.map_one],
  rw [nat.succ_eq_add_one, pow_succ', add_smul, one_smul, good_prime_mul_mod_p h _ hkp, t_ih],
  rw ← nat.prime.coprime_iff_not_dvd (fact.out p.prime) at hkp ⊢,
  exact nat.coprime.pow_right t hkp
end

end good_prime_props







section pstrong_maps

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} [fact p.prime] (f : additive_map M)

private lemma pstrong_mod_p_induct {a : ℕ} (h : good f (p ^ a))
  {k : ℕ} (hkp : ¬p ∣ k) (h0 : k < p ^ a) : f k = f (k % p) :=
begin
  have hp := fact.out p.prime,
  rcases a.eq_zero_or_pos with rfl | h1,
  rw [pow_zero, nat.lt_one_iff] at h0,
  rw [h0, nat.zero_mod],
  revert hkp h0 k h; refine nat.le_induction _ _ a h1; clear h1 a,
  rw pow_one; intros h k hkp h0,
  rw nat.mod_eq_of_lt h0,
  intros n hn1 n_ih h k h0 h1,
  induction k using nat.strong_induction_on with k k_ih,
  cases lt_or_le k (p ^ n) with h2 h2,
  exact n_ih (good_dc f _ (pow_ne_zero _ hp.ne_zero) h _ ⟨p, pow_succ' p n⟩) h0 h2,
  clear n_ih,

  let c := p ^ (n + 1) / k,
  let d := p ^ (n + 1) % k,
  have X : ∀ a b : ℕ, b % a ≠ 0 ↔ ¬a ∣ b := λ a b, by rw [ne.def, nat.dvd_iff_mod_eq_zero],
  have hk : k ≠ 0 := by rintros rfl; exact h0 ⟨0, by rw mul_zero⟩,
  have hc : c ≠ 0 := ne_of_gt (nat.div_pos (le_of_lt h1) (zero_lt_iff.mpr hk)),
  have hd : d ≠ 0 := begin
    rw [X, nat.dvd_prime_pow hp]; rintros ⟨t, ht, rfl⟩,
    rw pow_le_pow_iff hp.one_lt at h2,
    replace h2 := pow_dvd_pow p (le_trans hn1 h2),
    rw pow_one at h2; exact h0 h2
  end,
  replace h2 : c < p :=
  begin
    rw le_iff_eq_or_lt at h2,
    rcases h2 with rfl | h2,
    exfalso; apply h0,
    replace hn1 := pow_dvd_pow p hn1,
    rwa pow_one at hn1,
    rwa [nat.div_lt_iff_lt_mul (zero_lt_iff.mpr hk), pow_succ, mul_lt_mul_left hp.pos]
  end,
  have h3 : c * k + d = p ^ (n + 1) := nat.div_add_mod' _ k,
  rw [← add_right_inj (f c), ← additive_map.map_mul f hc hk, h _ _ (mul_ne_zero hc hk) hd h3],
  replace h3 : p ∣ d + c * k := ⟨p ^ n, by rw [add_comm, h3, pow_succ]⟩,
  have h4 : ¬p ∣ c := nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr hc) h2,
  have h5 := nat.prime.not_dvd_mul hp h4 h0,
  have h6 : ¬p ∣ d := λ h6, by rw nat.dvd_add_right h6 at h3; exact h5 h3,
  have h7 : d < k := (p ^ (n + 1)).mod_lt (zero_lt_iff.mpr hk),
  replace k_ih := k_ih d h7 h6 (lt_trans h7 h1),
  replace h : good f p := good_dc f _ (pow_ne_zero _ hp.ne_zero) h _ ⟨p ^ n, by rw pow_succ⟩,
  rw [k_ih, ← nat.mod_eq_of_lt h2, ← good_prime_mul_mod_p h h4 h0,
      h (c * k % p) (d % p) (by rwa X) (by rwa X)],
  rw [add_comm, ← nat.add_mod_add_of_le_add_mod, nat.mod_eq_zero_of_dvd h3, zero_add],
  exact nat.le_mod_add_mod_of_dvd_add_of_not_dvd h3 h6
end

private lemma pstrong_is_regular (h : strong p (good f)) : is_regular_map M p f :=
begin
  have hp := fact.out p.prime,
  rw is_regular_map.iff; intros t h0,
  refine pstrong_mod_p_induct f (h t) _ (nat.lt_pow_self hp.one_lt t),
  rwa [nat.coprime_comm, nat.prime.coprime_iff_not_dvd hp] at h0
end

private lemma regular_pstrong_iff (c : M) (χ : additive (zmod p)ˣ →+ M) :
  strong p (good (regular_map M p (c, χ))) ↔ χ (of_mul (-1)) = 0 :=
begin
  have hp := fact.out p.prime,
  have h0 := hp.one_lt,
  refine ⟨λ h, _, λ h, _⟩,
  { have h1 := ne_of_gt (nat.sub_pos_of_lt h0),
    replace h := h 1 1 (p - 1) one_ne_zero h1
      (by rw [pow_one, add_comm, nat.sub_add_cancel (le_of_lt h0)]),
    rwa [regular_map.map_ne_zero _ one_ne_zero, padic_val_nat.one, zero_smul, zero_add,
         regular_map.map_ne_zero _ h1, padic_val_nat.eq_zero_of_not_dvd, zero_smul, zero_add,
         zmod.ord_compl.map_coprime_p_dvd_add p.coprime_one_left (_ : p ∣ 1 + (p - 1)),
         zmod.ord_compl.map_one, of_mul_one, add_monoid_hom.map_zero, eq_comm] at h,
    rw [add_comm, nat.sub_add_cancel (le_of_lt h0)],
    intros h2; refine not_lt_of_le (nat.le_of_dvd (zero_lt_iff.mpr h1) h2) _,
    exact nat.sub_lt hp.pos one_pos },
  { intros t a b ha hb h1,
    rw [regular_map.map_ne_zero _ ha, regular_map.map_ne_zero _ hb,
        padic_add_eq_p_pow p ha hb h1, add_right_inj],
    obtain ⟨k, u, v, rfl, rfl, hu, hv⟩ : ∃ k u v : ℕ,
      p ^ k * u = a ∧ p ^ k * v = b ∧ p.coprime u ∧ p.coprime v :=
    begin
      refine ⟨padic_val_nat p a, ord_compl[p] a, ord_compl[p] b, _, _,
        nat.coprime_ord_compl hp ha, nat.coprime_ord_compl hp hb⟩,
      rw [← nat.factorization_def _ hp, nat.ord_proj_mul_ord_compl_eq_self],
      rw [padic_add_eq_p_pow p ha hb h1, ← nat.factorization_def _ hp,
          nat.ord_proj_mul_ord_compl_eq_self]
    end,
    clear ha hb; rw ← mul_add at h1,
    rw nat.coprime_comm at hu hv,
    rw [zmod.ord_compl.map_self_pow_mul, zmod.ord_compl.map_self_pow_mul],
    suffices : zmod.ord_compl p v = -zmod.ord_compl p u,
      rw [this, ← neg_one_mul, of_mul_mul, add_monoid_hom.map_add, h, zero_add],
    clear h c χ _inst_1 M; refine zmod.ord_compl.map_coprime_p_dvd_add hu _,
    have h2 : p ^ k ∣ p ^ t := ⟨u + v, h1.symm⟩,
    rw [nat.pow_dvd_pow_iff_le_right h0, le_iff_exists_add] at h2,
    rcases h2 with ⟨c, rfl⟩,
    rw [pow_add, mul_eq_mul_left_iff, or_iff_left (pow_ne_zero _ hp.ne_zero)] at h1,
    use p ^ (c - 1); rw [h1, ← pow_succ, nat.sub_add_cancel],
    rw [← not_lt, nat.lt_one_iff]; rintros rfl,
    rw [pow_zero, nat.add_eq_one_iff] at h1,
    have X : ¬nat.coprime 0 p := by rw nat.coprime_zero_left; exact ne_of_gt h0,
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
    exacts [X hu, X hv] }
end

/-- Characterizations of `p`-strong maps -/
theorem pstrong_iff : strong p (good f) ↔
  ∃ (c : M) (χ : additive (zmod p)ˣ →+ M), χ (of_mul (-1)) = 0 ∧ f = regular_map M p (c, χ) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨⟨c, χ⟩, rfl⟩ := pstrong_is_regular f h,
    rw regular_pstrong_iff at h,
    exact ⟨c, χ, h, rfl⟩ },
  { rcases h with ⟨c, χ, h, rfl⟩,
    rw regular_pstrong_iff; exact h }
end

end pstrong_maps







section torsion_free

variables {M : Type*} [add_cancel_comm_monoid M] [no_zero_smul_divisors ℕ M]

private lemma torsion_free_good_vals {f : additive_map M} {p : ℕ} (h : p.prime) (h0 : good f p)
  {k : ℕ} (h1 : k ≠ 0) (h2 : k < p) : f k = 0 :=
begin
  haveI : fact p.prime := ⟨h⟩,
  have h3 := nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr h1) h2,
  have h4 := good_prime_pow_mod_p h0 h3 p.totient,
  rw [← h.coprime_iff_not_dvd, nat.coprime_comm] at h3,
  replace h3 := nat.modeq.pow_totient h3,
  rw [nat.modeq, nat.mod_eq_of_lt h.one_lt] at h3,
  rw [h3, additive_map.map_one, nat.mod_eq_of_lt h2, eq_comm, smul_eq_zero, or_comm] at h4,
  cases h4 with h4 h4,
  exact h4,
  exfalso; exact ne_of_gt (nat.totient_pos h.pos) h4
end

private lemma torsion_free_wide_maps {f : additive_map M} : wide (good f) ↔ f = 0 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { ext k; rw zero_apply,
    rcases eq_or_ne k 0 with rfl | h0,
    rw additive_map.map_zero,
    obtain ⟨p, ⟨h1, h2⟩, h3⟩ := set.infinite.exists_gt h k,
    exact torsion_free_good_vals h1 h2 h0 h3 },
  { subst h; unfold wide,
    convert nat.infinite_set_of_prime; ext p,
    refine and_iff_left (λ a b _ _ _, _),
    rw [additive_map.zero_apply, additive_map.zero_apply] }
end

private lemma torsion_free_pstrong_maps {f : additive_map M} {p : ℕ} (h : p.prime) :
  strong p (good f) ↔ (f : ℕ → M) = λ n, padic_val_nat p n • f p :=
begin
  haveI _inst_3 : fact p.prime := ⟨h⟩,
  refine ⟨λ h0, _, λ h0 k a b ha hb h, _⟩,
  { replace h : ∀ k : ℕ, k ≠ 0 → k < p → f k = 0 :=
      λ k, torsion_free_good_vals h (by convert h0 1; rw pow_one),
    rw pstrong_iff at h0,
    rcases h0 with ⟨c, χ, -, rfl⟩; ext x,
    rw ← regular_map.snd_eq_zero_iff at h; simp only [] at h; subst h,
    rcases eq_or_ne x 0 with rfl | h0,
    rw [regular_map.map_zero, padic_val_nat.zero, zero_smul],
    rw [regular_map.map_p, regular_map.map_ne_zero _ h0],
    simp only [add_monoid_hom.zero_apply, add_zero] },
  { rw h0; simp only [],
    rw padic_add_eq_p_pow p ha hb h }
end

/-- Characterizations of additive maps `f` with infinitely many `f`-good positive integers. -/
theorem good_infinite_iff_wide_case (f : additive_map M) : (set_of (good f)).infinite ↔
  ∃ p : ℕ, p.prime ∧ (f : ℕ → M) = λ n, padic_val_nat p n • f p :=
begin
  rw [good_infinite_iff_wide_or_strong, torsion_free_wide_maps]; split,
  { rintros (rfl | ⟨p, hp, h⟩),
    refine ⟨2, nat.prime_two, _⟩,
    ext x; rw [additive_map.zero_apply, additive_map.zero_apply, smul_zero],
    exact ⟨p, hp, (torsion_free_pstrong_maps hp).mp h⟩ },
  { rintros ⟨p, hp, h⟩,
    right; exact ⟨p, hp, (torsion_free_pstrong_maps hp).mpr h⟩ }
end

end torsion_free







section wide_map_construction

variables {M : Type*} [add_comm_monoid M]

private lemma wide_if_χ₄_eq_one {c : M} (hc : 2 • c = 0) {p : legendre_stack} (h : p.χ₄ = 1) :
  wide (good (p.map c hc)) :=
begin
  refine set.infinite_of_injective_forall_mem p.ascending.injective (λ n, ⟨p.is_prime n, _⟩),
  intros a b ha hb h0,
  replace hb : a < p n := by rwa [← h0, lt_add_iff_pos_right, zero_lt_iff],
  rw [eq_comm, add_comm, ← nat.sub_eq_iff_eq_add (le_of_lt hb)] at h0,
  rw [← p.map_p_sub_χ₄_eq_one hc h ha hb, h0]
end

/-- Non-zero wide map exists over `M` if `M` is not 2-torsion free. -/
theorem exists_nonzero_wide_if_not_two_torsion_free (h : ∃ c : M, c ≠ 0 ∧ 2 • c = 0) :
  ∃ f : additive_map M, f ≠ 0 ∧ wide (good f) :=
begin
  rcases h with ⟨c, h, hc⟩,
  cases exists_legendre_stack_χ₄_eq_one with p hp,
  exact ⟨p.map c hc, p.map_is_non_zero hc h, wide_if_χ₄_eq_one hc hp⟩
end

/-- Non-zero wide map exists over `zmod 2`. -/
theorem exists_nonzero_wide_zmod2 : ∃ f : additive_map (zmod 2), f ≠ 0 ∧ wide (good f) :=
  exists_nonzero_wide_if_not_two_torsion_free
    ⟨1, one_ne_zero, by rw [nat.smul_one_eq_coe, nat.cast_two]; refl⟩

end wide_map_construction







section wide_regular_distinction

/-- Wide regular maps must be zero -/
theorem wide_regular_map_is_zero {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} [fact p.prime]
  {f : additive_map M} (h : is_regular_map M p f) (h0 : wide (good f)) : f = 0 :=
begin
  rw is_regular_map.zero_iff_at_le_p h,
  intros k h1 h2,
  rw is_regular_map.iff at h,
  replace h0 := set.infinite.exists_gt h0 (p * p),
  rcases h0 with ⟨q, ⟨h0, h3⟩, h4⟩,
  have X := (fact.out p.prime).ne_zero,
  have X0 : k * p < q := lt_of_le_of_lt (mul_le_mul_right' h2 p) h4,
  have X1 : p < q := lt_of_le_of_lt p.le_mul_self h4,
  have X2 : q.coprime p := (nat.coprime_primes h0 (fact.out p.prime)).mpr (ne_of_gt X1),
  rw [← add_left_inj (f p), zero_add, ← additive_map.map_mul f h1 X,
      h3 (k * p) (q - k * p) (mul_ne_zero h1 X) (ne_of_gt (by rwa tsub_pos_iff_lt)),
      h3 p (q - p) X (ne_of_gt (by rwa tsub_pos_iff_lt)), h, h (q - p)],
  congr' 1,
  rw [← nat.add_mul_mod_self_right _ k, nat.sub_add_cancel (le_of_lt X0),
      ← nat.add_mod_right (q - p) p, nat.sub_add_cancel (le_of_lt X1)],
  rwa [← nat.coprime_add_self_left, nat.sub_add_cancel (le_of_lt X1)],
  rwa [← nat.coprime_add_mul_right_left _ _ k, nat.sub_add_cancel (le_of_lt X0)],
  rw [add_comm, nat.sub_add_cancel (le_of_lt X1)],
  rw [add_comm, nat.sub_add_cancel (le_of_lt X0)]
end

end wide_regular_distinction

end IMO2020N5
end IMOSL
