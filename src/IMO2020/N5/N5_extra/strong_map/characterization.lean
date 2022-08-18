import IMO2020.N5.N5_extra.strong_map.construction IMO2020.N5.N5_extra.strong_map.lemmas

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
  rw [pmix_inv_hom_pair, pmix_hom_apply, ppow_part_hom_apply, pcop_part_hom_apply_eq_fn],
  convert (pstrong_val f h).symm,
  rw [zmod.pcop_part, dif_neg h, zmod.coe_unit_of_coprime, zmod.val_nat_cast]
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

end strong_map







namespace additive_map

open strong_map

variables {M : Type*} [add_cancel_comm_monoid M] (p : ℕ) [fact p.prime]

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

end IMO2020N5
end IMOSL
