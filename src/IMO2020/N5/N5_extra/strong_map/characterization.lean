import IMO2020.N5.N5_extra.strong_map.construction

/-!
# Characterization of `p`-strong maps

We characterize `p`-strong additive maps, where `p` is a prime.
That is, we prove that `pmix_map M p` is in fact bijective.
Then we construct the corresponding isomorphism.
The main constructions are as follows.
* `ppow_part_hom M p : strong_map M p →+ M`, the map sending `f` to the `p`-power part of `f`.
* `pcop_part_hom M p : strong_map M p →+ pcompl_hom M p`, the map sending `f` to the
    `p`-coprime part `χ` of `f`, defined by `χ(n) = f(n)` for each `1 ≤ n < p`.
* `pmix_inv_hom M p`, the representation of `f` in `M × pcompl_hom M p`.
  It is the product map of `ppow_part_hom M p` and `pcop_part_hom M p`.
  This map is the inverse map corresponding to `pmix_hom M p`.
* `pmix_equiv M p` is the isomorphism `(M × pcompl_hom M p) ≃+ strong_map M p`
    obtained from `pmix_hom M p` with inverse `pmix_inv_hom M p`.
* Using `pmix_equiv M p`, we can state characterization of `p`-strong maps using additive maps.
  This is the theorem `pstrong_iff` in namespace `additive_map`.
-/

namespace IMOSL
namespace IMO2020N5



section extra_lemmas

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} [fact p.prime]

private lemma pstrong_mod_p_induct (f : additive_map M) {a : ℕ} (h : good (p ^ a) f)
  {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) (h0 : k < p ^ a) : f k = f (k % p) :=
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
  exact n_ih (good_factor f (pow_ne_zero _ hp.ne_zero) h ⟨p, pow_succ' p n⟩) h0 h2,
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
  rw [← add_right_inj (f c), ← additive_map.map_mul_add f hc hk, h _ _ (mul_ne_zero hc hk) hd h3],
  replace h3 : p ∣ d + c * k := ⟨p ^ n, by rw [add_comm, h3, pow_succ]⟩,
  have h4 : ¬p ∣ c := nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr hc) h2,
  have h5 := nat.prime.not_dvd_mul hp h4 h0,
  have h6 : ¬p ∣ d := λ h6, by rw nat.dvd_add_right h6 at h3; exact h5 h3,
  have h7 : d < k := (p ^ (n + 1)).mod_lt (zero_lt_iff.mpr hk),
  replace k_ih := k_ih d h7 h6 (lt_trans h7 h1),
  replace h : good p f := good_factor f (pow_ne_zero _ hp.ne_zero) h ⟨p ^ n, by rw pow_succ⟩,
  rw [k_ih, ← nat.mod_eq_of_lt h2, ← good_prime_mul_mod_p f hp h h4 h0,
      h (c * k % p) (d % p) (by rwa X) (by rwa X)],
  rw [add_comm, ← nat.add_mod_add_of_le_add_mod, nat.mod_eq_zero_of_dvd h3, zero_add],
  exact nat.le_mod_add_mod_of_dvd_add_of_not_dvd h3 h6
end

open strong_map

private theorem pstrong_mod_p (f : strong_map M p) {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) : f k = f (k % p) :=
  pstrong_mod_p_induct f (is_strong f k) hkp (nat.lt_pow_self (fact.out p.prime).one_lt k)

private theorem pstrong_val (f : strong_map M p) {x : ℕ} (h : x ≠ 0) :
  f x = padic_val_nat p x • f p + f (zmod.pcop_part p x : zmod p).val :=
  let hp := fact.out p.prime in by rw [zmod.pcop_part, dif_neg h, zmod.coe_unit_of_coprime,
    zmod.val_nat_cast, ← pstrong_mod_p f (nat.not_dvd_ord_compl hp h), ← map_pow_smul f hp.ne_zero,
    ← map_mul_add f (pow_ne_zero _ hp.ne_zero) (ne_of_gt (nat.ord_compl_pos p h)),
    ← nat.factorization_def x hp, nat.ord_proj_mul_ord_compl_eq_self]

end extra_lemmas







namespace strong_map

variables (M : Type*) [add_cancel_comm_monoid M] (p : ℕ) [fact p.prime]



section ppow_part_hom

/-- The `p`-power part of a strong map -/
def ppow_part_hom : strong_map M p →+ M :=
{ to_fun := λ f, f p,
  map_zero' := zero_apply,
  map_add' := λ f g, add_apply }

@[simp] lemma ppow_part_hom_apply (f : strong_map M p) : ppow_part_hom M p f = f p := rfl

lemma ppow_part_hom_of_ppow (c : M) : ppow_part_hom M p (ppow_hom M p c) = c :=
  by rw [ppow_part_hom_apply, ppow_hom_p]

lemma ppow_part_hom_of_pcop (χ : pcompl_hom M p) : ppow_part_hom M p (pcop_hom M p χ) = 0 :=
  by rw [ppow_part_hom_apply, pcop_hom_p]

end ppow_part_hom



section pcop_part_hom

/-- The `p`-coprime part of a strong map, in functional value -/
def pcop_part_fn (f : strong_map M p) (x : (zmod p)ˣ) := f (x : zmod p).val

lemma pcop_part_map_one {f : strong_map M p} : pcop_part_fn M p f 1 = 0 :=
  by rw [pcop_part_fn, units.coe_one, zmod.val_one p, map_one_zero]

lemma pcop_part_map_mul {f : strong_map M p} (x y : (zmod p)ˣ) :
  pcop_part_fn M p f (x * y) = pcop_part_fn M p f x + pcop_part_fn M p f y :=
begin
  dsimp only [pcop_part_fn],
  suffices : ∀ t : (zmod p)ˣ, ¬p ∣ (t : zmod p).val,
  { have h : ∀ t : (zmod p)ˣ, (t : zmod p).val ≠ 0 :=
      λ t, by rw [ne.def, zmod.val_eq_zero]; exact units.ne_zero t,
    rw [units.coe_mul, zmod.val_mul, ← pstrong_mod_p, map_mul_add f (h x) (h y)],
    exact (fact.out p.prime).not_dvd_mul (this x) (this y) },
  intros t,
  rw [← zmod.nat_coe_zmod_eq_zero_iff_dvd, zmod.nat_cast_val, zmod.cast_id', id.def],
  exact t.ne_zero
end

lemma pcop_part_map_neg_one {f : strong_map M p} : pcop_part_fn M p f (-1) = 0 :=
begin
  suffices : (-1 : zmod p).val = p - 1,
  { rw [pcop_part_fn, units.coe_neg_one, this, is_strong f 1 _ 1 _ one_ne_zero, map_one_zero],
    rw [pow_one, nat.sub_add_cancel (le_of_lt (fact.out p.prime).one_lt)],
    exact ne_of_gt (nat.sub_pos_of_lt (fact.out p.prime).one_lt) },
  rw [zmod.neg_val, if_neg, zmod.val_one],
  exact one_ne_zero
end

/-- The `p`-coprime part of a strong map, as a pure function -/
def pcop_part (f : strong_map M p) : pcompl_hom M p :=
{ to_fun := pcop_part_fn M p f,
  map_zero' := pcop_part_map_one M p,
  map_add' := pcop_part_map_mul M p,
  map_neg_one' := pcop_part_map_neg_one M p }

lemma pcop_part_apply_eq_fn (f : strong_map M p) (x : (zmod p)ˣ) :
  pcop_part M p f x = f (x : zmod p).val := rfl

lemma pcop_part_zero : pcop_part M p 0 = 0 :=
  by ext; rw [pcop_part_apply_eq_fn, zero_apply, pcompl_hom.zero_apply]

lemma pcop_part_add (f g : strong_map M p) :
  pcop_part M p (f + g) = pcop_part M p f + pcop_part M p g :=
  by ext; simp only [pcop_part_apply_eq_fn, pcompl_hom.add_apply, add_apply]

lemma pcop_part_eq_iff (f : strong_map M p) (χ : pcompl_hom M p) :
  pcop_part M p f = χ ↔ ∀ n : ℕ, n ≠ 0 → n < p → f n = χ (zmod.pcop_part p n) :=
begin
  have hp := fact.out p.prime,
  split,
  { rintros rfl n h h0,
    rw [pcop_part_apply_eq_fn, zmod.pcop_val p h, eq_ord_compl_of_coprime hp, nat.mod_eq_of_lt h0],
    rw hp.coprime_iff_not_dvd; exact nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr h) h0 },
  { intros h; ext,
    have h0 : (x : zmod p).val ≠ 0 := by rw [ne.def, zmod.val_eq_zero]; exact units.ne_zero x,
    have h1 : (x : zmod p).val < p := zmod.val_lt _,
    rw [pcop_part_apply_eq_fn, h _ h0 h1]; apply congr_arg,
    rw ← units.eq_iff; apply zmod.val_injective,
    rw [zmod.pcop_val _ h0, eq_ord_compl_of_coprime hp, nat.mod_eq_of_lt h1],
    rw hp.coprime_iff_not_dvd; exact nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr h0) h1 }
end

lemma pcop_part_eq_zero_iff (f : strong_map M p) :
  pcop_part M p f = 0 ↔ ∀ n : ℕ, n ≠ 0 → n < p → f n = 0 :=
  by rw pcop_part_eq_iff; simp only [pcompl_hom.zero_apply]

/-- The `p`-coprime part of a strong map -/
def pcop_part_hom : strong_map M p →+ pcompl_hom M p :=
{ to_fun := pcop_part M p,
  map_zero' := pcop_part_zero M p,
  map_add' := pcop_part_add M p }

@[simp] lemma pcop_part_hom_apply_eq_fn (f : strong_map M p) (x : (zmod p)ˣ) :
  pcop_part_hom M p f x = f (x : zmod p).val := rfl

lemma pcop_part_hom_eq_iff (f : strong_map M p) (χ : pcompl_hom M p) :
  pcop_part_hom M p f = χ ↔ ∀ n : ℕ, n ≠ 0 → n < p → f n = χ (zmod.pcop_part p n) :=
  pcop_part_eq_iff M p f χ

lemma pcop_part_hom_eq_zero_iff (f : strong_map M p) :
  pcop_part_hom M p f = 0 ↔ ∀ n : ℕ, n ≠ 0 → n < p → f n = 0 :=
  pcop_part_eq_zero_iff M p f

lemma pcop_part_hom_of_ppow (c : M) : pcop_part_hom M p (ppow_hom M p c) = 0 :=
begin
  rw pcop_part_hom_eq_zero_iff; intros n h h0,
  rw [ppow_hom_val, padic_val_nat.eq_zero_of_not_dvd, zero_smul],
  exact nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr h) h0
end

lemma pcop_part_hom_of_pcop (χ : pcompl_hom M p) : pcop_part_hom M p (pcop_hom M p χ) = χ :=
begin
  rw pcop_part_hom_eq_iff; intros n h h0,
  rw [pcop_hom_val, if_neg h]
end

end pcop_part_hom



section pmix_inv_hom

/-- The inverse map of `pmix_hom M p` -/
def pmix_inv_hom : strong_map M p →+ M × pcompl_hom M p :=
  add_monoid_hom.prod (ppow_part_hom M p) (pcop_part_hom M p)

@[simp] theorem pmix_inv_hom_pair (f : strong_map M p) :
  pmix_inv_hom M p f = (ppow_part_hom M p f, pcop_part_hom M p f) := rfl

theorem pmix_inv_if_left_inverse : function.left_inverse (pmix_inv_hom M p) (pmix_hom M p) :=
  λ ⟨c, x⟩, by rw [pmix_hom_pair, pmix_inv_hom_pair, map_add, map_add, ppow_part_hom_of_ppow,
    ppow_part_hom_of_pcop, add_zero, pcop_part_hom_of_ppow, pcop_part_hom_of_pcop, zero_add]

theorem pmix_inv_if_right_inverse : function.right_inverse (pmix_inv_hom M p) (pmix_hom M p) :=
begin
  intros f; ext x,
  rcases eq_or_ne x 0 with rfl | h,
  rw [map_zero, map_zero],
  rw [pmix_inv_hom_pair, pmix_hom_apply, ppow_part_hom_apply,
      pcop_part_hom_apply_eq_fn, ← pstrong_val f h]
end

end pmix_inv_hom



section pmix_equiv

/-- The equivalence between `M × pcompl_hom M p` and `strong_map M p`. -/
def pmix_equiv : M × pcompl_hom M p ≃+ strong_map M p :=
{ inv_fun := pmix_inv_hom M p,
  left_inv := pmix_inv_if_left_inverse M p,
  right_inv := pmix_inv_if_right_inverse M p,
  .. pmix_hom M p }

@[simp] theorem pmix_equiv_pair (c : M) (χ : pcompl_hom M p) :
  pmix_equiv M p (c, χ) = ppow_hom M p c + pcop_hom M p χ := rfl

@[simp] theorem pmix_equiv_apply (c : M) (χ : pcompl_hom M p) (n : ℕ) :
  pmix_equiv M p (c, χ) n = padic_val_nat p n • c + χ (zmod.pcop_part p n) :=
  pmix_hom_apply M p c χ n

end pmix_equiv







namespace additive_map

/-- Characterization of `p`-strong maps, in the language of additive maps. -/
theorem pstrong_iff (f : additive_map M) : strong p f ↔ ∃ (c : M) (χ : pcompl_hom M p),
  ∀ n : ℕ, f n = padic_val_nat p n • c + χ (zmod.pcop_part p n) :=
begin
  split,
  { intros h,
    set g : strong_map M p := ⟨f, h⟩ with hg,
    let pair := (pmix_equiv M p).symm g,
    refine ⟨pair.fst, pair.snd, λ n, _⟩,
    rw [← pmix_equiv_apply, prod.mk.eta, add_equiv.apply_symm_apply, hg],
    refl },
  { rintros ⟨c, χ, h⟩,
    suffices : f = (pmix_equiv M p (c, χ)).to_additive_map,
      rw this; exact is_strong (pmix_equiv M p (c, χ)),
    ext; rw [h, ← pmix_equiv_apply]; refl }
end

end additive_map

end strong_map

end IMO2020N5
end IMOSL
