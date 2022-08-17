import
  IMO2020.N5.N5_extra.strong_map.basic
  IMO2020.N5.N5_extra.strong_map.pcompl_hom

/-!
# Construction of `p`-strong maps

We construct the `p`-strong map structure and also some important examples of `p`-strong maps.
* Given `x : M`, the pure `p`-power strong map `ppow_map M p x` is the map `n ↦ ν_p(n) • x`
    as a `p`-strong map, with corresponding homomorphism `ppow_hom M p`.
* Given `χ : pcompl_hom M p`, the pure `p`-coprime strong map `pcop_map M p χ` is the map
    `n ↦ χ((n / p^ν_p(n)) % p)` as a `p`-strong map, with corresponding homomorphism `pcop_hom M p`.
* The strong homomorphism `pmix_hom M p` is the coproduct of `ppow_hom M p` and `pcop_hom M p`.
  As a `p`-strong map, it equals `ppow_map M p x + pcop_map M p χ`.

It turns out that `pmix_map M p` is a bijection.
We prove this result and construct the isomorphism in `characterization.lean`.
-/

namespace IMOSL
namespace IMO2020N5

open strong_map



namespace zmod

variables (p : ℕ) [fact (p.prime)]

@[simp] lemma unit_of_coprime_one {h : nat.coprime 1 p} : zmod.unit_of_coprime 1 h = 1 :=
  by simp only [zmod.unit_of_coprime, nat.cast_one, inv_one]; refl



/-- The `p`-coprime part of a positive natural, embedded into `(zmod p)ˣ`.
  If `n = 0`, we define the `p`-coprime part to be `1` in `(zmod p)ˣ`. -/
def pcop_part (n : ℕ) : (zmod p)ˣ :=
  dite (n = 0) (λ _, 1) (λ h : n ≠ 0, zmod.unit_of_coprime (ord_compl[p] n)
    (nat.coprime_comm.mp (nat.coprime_ord_compl (fact.out p.prime) h)))

@[simp] lemma pcop_zero : pcop_part p 0 = 1 :=
  by rw [pcop_part, dif_pos rfl]

@[simp] lemma pcop_one : pcop_part p 1 = 1 :=
  by simp only [pcop_part, dif_neg one_ne_zero, nat.factorization_one,
    finsupp.coe_zero, pi.zero_apply, pow_zero, nat.div_one, unit_of_coprime_one]

@[simp] lemma pcop_ppow (k : ℕ) : pcop_part p (p ^ k) = 1 :=
begin
  have hp := fact.out p.prime,
  rw [pcop_part, dif_neg (pow_ne_zero k hp.ne_zero)],
  convert unit_of_coprime_one p,
  rw [nat.prime.factorization_pow hp, finsupp.single_eq_same, nat.div_self],
  exacts [pow_pos hp.pos k, nat.coprime_one_left p]
end
  
@[simp] lemma pcop_p : pcop_part p p = 1 :=
  by convert pcop_ppow p 1; rw pow_one

@[simp] lemma pcop_val {n : ℕ} (h : n ≠ 0) :
  (zmod.pcop_part p n : zmod p).val = ord_compl[p] n % p :=
  by rw [zmod.pcop_part, dif_neg h, zmod.coe_unit_of_coprime, zmod.val_nat_cast]

theorem pcop_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
  pcop_part p (m * n) = pcop_part p m * pcop_part p n :=
begin
  rw ← units.eq_iff,
  simp only [pcop_part, zmod.unit_of_coprime, units.coe_mul],
  rw [dif_neg hm, dif_neg hn, dif_neg (mul_ne_zero hm hn)],
  simp only [units.coe_mk],
  rw [nat.ord_compl_mul, nat.cast_mul]
end

end zmod



section extra_lemmas

lemma eq_ord_compl_of_coprime {p : ℕ} (h : p.prime) {n : ℕ} (h0 : p.coprime n) : ord_compl[p] n = n :=
begin
  rw [(nat.factorization_eq_zero_iff' n p).mpr, pow_zero, nat.div_one],
  right; left; rwa ← h.coprime_iff_not_dvd
end



section add_eq_ppow

variables (p : ℕ) [fact (p.prime)] {a b k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a + b = p ^ k)
include ha hb h

private lemma padic_add_eq_p_pow' : padic_val_nat p a ≤ padic_val_nat p b :=
begin
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

lemma padic_add_eq_p_pow : padic_val_nat p a = padic_val_nat p b :=
  le_antisymm (padic_add_eq_p_pow' p ha hb h) (padic_add_eq_p_pow' p hb ha (by rwa add_comm))

lemma nat_pcop_part_add_eq_p_pow : p ∣ ord_compl[p] a + ord_compl[p] b :=
begin
  let h0 : ∀ n : ℕ, n.factorization p = padic_val_nat p n :=
    λ n, nat.factorization_def n (fact.out p.prime),
  rw [h0, padic_add_eq_p_pow p ha hb h, ← h0, ← nat.add_div_of_dvd_left, h, h0],
  clear h0,
  work_on_goal 2 { exact nat.ord_proj_dvd b p },
  suffices : padic_val_nat p b < k,
  { use p ^ (k - padic_val_nat p b - 1),
    rw [← pow_succ, nat.pow_div (le_of_lt this) (fact.out p.prime).pos, nat.sub_add_cancel],
    exact nat.sub_pos_of_lt this },
  replace h : ¬p^k ∣ b := nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr hb)
    (by rwa [← h, lt_add_iff_pos_left, zero_lt_iff]),
  rw padic_val_nat_dvd_iff at h; contrapose! h,
  right; exact h
end

lemma zmod_pcop_part_add_eq_p_pow : -zmod.pcop_part p a = zmod.pcop_part p b :=
begin
  rw ← units.eq_iff,
  simp only [zmod.pcop_part, zmod.unit_of_coprime, units.coe_neg],
  rw [dif_neg ha, dif_neg hb, ← add_eq_zero_iff_neg_eq, units.coe_mk,
      units.coe_mk, ← nat.cast_add, zmod.nat_coe_zmod_eq_zero_iff_dvd],
  exact nat_pcop_part_add_eq_p_pow p ha hb h
end

end add_eq_ppow

end extra_lemmas







namespace strong_map

variables (M : Type*) [add_comm_monoid M] (p : ℕ) [fact p.prime]

/-- The pure `p`-power strong map -/
def ppow_map (x : M) : strong_map M p :=
{ to_fun := λ n, padic_val_nat p n • x,
  map_zero' := by rw [padic_val_nat.zero, zero_smul],
  map_mul_add' := λ x y hx hy, by rw [padic_val_nat.mul p hx hy, add_smul],
  is_strong' := λ k a b ha hb h, by simp only []; rw padic_add_eq_p_pow p ha hb h }

@[simp] theorem ppow_map_val (x : M) (n : ℕ) : ppow_map M p x n = padic_val_nat p n • x := rfl

@[simp] theorem ppow_map_ppow (x : M) (k : ℕ) : ppow_map M p x (p ^ k) = k • x :=
  by rw [ppow_map_val, padic_val_nat.prime_pow]

@[simp] theorem ppow_map_p (x : M) : ppow_map M p x p = x :=
  by rw [ppow_map_val, padic_val_nat_self, one_nsmul]

@[simp] theorem ppow_map_zero : ppow_map M p 0 = 0 :=
  by ext; rw [ppow_map_val, nsmul_zero, zero_apply]

@[simp] theorem ppow_map_add (x y : M) : ppow_map M p (x + y) = ppow_map M p x + ppow_map M p y :=
  by ext; simp only [add_apply, ppow_map_val, nsmul_add]

@[simp] theorem ppow_map_nsmul (n : ℕ) (x : M) : ppow_map M p (n • x) = n • ppow_map M p x :=
  by ext; rw [ppow_map_val, smul_def, ppow_map_val, nsmul_left_comm]

theorem ppow_map_inj {x y : M} : ppow_map M p x = ppow_map M p y ↔ x = y :=
begin
  refine ⟨λ h, _, λ h, by rw h⟩,
  replace h := fun_like.congr_fun h p,
  rwa [ppow_map_p, ppow_map_p] at h
end

/-- The pure `p`-power strong map, as a homomorphism -/
def ppow_hom : M →+ strong_map M p := ⟨ppow_map M p, ppow_map_zero M p, ppow_map_add M p⟩

@[simp] theorem ppow_hom_val (x : M) (n : ℕ) : ppow_hom M p x n = padic_val_nat p n • x := rfl

@[simp] theorem ppow_hom_ppow (x : M) (k : ℕ) : ppow_hom M p x (p ^ k) = k • x :=
  by rw [ppow_hom_val, padic_val_nat.prime_pow]

@[simp] theorem ppow_hom_p (x : M) : ppow_hom M p x p = x :=
  by rw [ppow_hom_val, padic_val_nat_self, one_nsmul]



/-- The pure `p`-coprime strong map -/
def pcop_map (χ : pcompl_hom M p) : strong_map M p :=
{ to_fun := λ n, ite (n = 0) 0 (χ (zmod.pcop_part p n)),
  map_zero' := rfl,
  map_mul_add' := λ x y hx hy, by rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy),
    zmod.pcop_mul p hx hy, pcompl_hom.map_mul_add χ],
  is_strong' := λ k a b ha hb h, by simp only []; rw [if_neg ha, if_neg hb,
    ← zmod_pcop_part_add_eq_p_pow p ha hb h, ← neg_one_mul, pcompl_hom.map_mul_add,
    pcompl_hom.map_neg_one, zero_add] }

@[simp] theorem pcop_map_val (χ : pcompl_hom M p) (n : ℕ) :
  pcop_map M p χ n = ite (n = 0) 0 (χ (zmod.pcop_part p n)) := rfl

@[simp] theorem pcop_map_zero : pcop_map M p 0 = 0 :=
  by ext; simp only [pcop_map_val, zero_apply, pcompl_hom.zero_apply, if_t_t]

@[simp] theorem pcop_map_apply_zero (χ : pcompl_hom M p) : pcop_map M p χ 0 = 0 := rfl

@[simp] theorem pcop_map_apply_ne_zero (χ : pcompl_hom M p) {n : ℕ} (h : n ≠ 0) :
  pcop_map M p χ n = χ (zmod.pcop_part p n) :=
  by rw [pcop_map_val, if_neg h]

@[simp] theorem pcop_map_ppow (χ : pcompl_hom M p) (k : ℕ) : pcop_map M p χ (p ^ k) = 0 :=
  by rw [pcop_map_apply_ne_zero M p χ (pow_ne_zero _ (fact.out p.prime).ne_zero),
         zmod.pcop_ppow, pcompl_hom.map_one]

@[simp] theorem pcop_map_p (χ : pcompl_hom M p) : pcop_map M p χ p = 0 :=
  by rw [pcop_map_apply_ne_zero M p χ (fact.out p.prime).ne_zero, zmod.pcop_p, pcompl_hom.map_one]

@[simp] theorem pcop_map_add (χ φ : pcompl_hom M p) :
  pcop_map M p (χ + φ) = pcop_map M p χ + pcop_map M p φ :=
begin
  ext x; rcases eq_or_ne x 0 with rfl | h,
  rw [add_apply, pcop_map_apply_zero, pcop_map_apply_zero, pcop_map_apply_zero, zero_add],
  rw add_apply; repeat { rw pcop_map_apply_ne_zero M p _ h }; rw pcompl_hom.add_apply
end

@[simp] theorem pcop_map_nsmul (n : ℕ) (χ : pcompl_hom M p) :
  pcop_map M p (n • χ) = n • pcop_map M p χ :=
begin
  ext x; rcases eq_or_ne x 0 with rfl | h,
  rw [pcop_map_apply_zero, smul_def, pcop_map_apply_zero, smul_zero],
  rw smul_def; repeat { rw pcop_map_apply_ne_zero M p _ h }; rw pcompl_hom.nsmul_apply
end

theorem pcop_map_inj {χ φ : pcompl_hom M p} : pcop_map M p χ = pcop_map M p φ ↔ χ = φ :=
begin
  refine ⟨λ h, _, λ h, by rw h⟩,
  ext n,
  have h0 := n.ne_zero,
  rw [ne.def, ← zmod.val_eq_zero, ← ne.def] at h0,
  suffices : n = zmod.pcop_part p (n : zmod p).val,
  { replace h := fun_like.congr_fun h (n : zmod p).val,
    rwa [pcop_map_apply_ne_zero M p χ h0, pcop_map_apply_ne_zero M p φ h0, ← this] at h },
  rw [← units.eq_iff, zmod.pcop_part, dif_neg h0, zmod.coe_unit_of_coprime],
  replace h0 : ((n : zmod p).val : zmod p) = (n : zmod p) :=
    by rw [zmod.nat_cast_val, zmod.cast_id', id.def],
  rw [eq_ord_compl_of_coprime (fact.out p.prime), h0],
  rw [(fact.out p.prime).coprime_iff_not_dvd, ← zmod.nat_coe_zmod_eq_zero_iff_dvd, h0],
  exact units.ne_zero n
end

/-- The pure `p`-coprime strong map, as a homomorphism -/
def pcop_hom : pcompl_hom M p →+ strong_map M p :=
  ⟨pcop_map M p, pcop_map_zero M p, pcop_map_add M p⟩

@[simp] theorem pcop_hom_val (χ : pcompl_hom M p) (n : ℕ) :
  pcop_hom M p χ n = ite (n = 0) 0 (χ (zmod.pcop_part p n)) := rfl

theorem pcop_hom_apply_ne_zero (χ : pcompl_hom M p) {n : ℕ} (h : n ≠ 0) :
  pcop_hom M p χ n = χ (zmod.pcop_part p n) := by rw [pcop_hom_val, if_neg h]

@[simp] theorem pcop_hom_ppow (χ : pcompl_hom M p) (k : ℕ) : pcop_hom M p χ (p ^ k) = 0 :=
  by rw [pcop_hom_apply_ne_zero M p χ (pow_ne_zero k (fact.out p.prime).ne_zero),
         zmod.pcop_ppow, pcompl_hom.map_one]

@[simp] theorem pcop_hom_p (χ : pcompl_hom M p) : pcop_hom M p χ p = 0 :=
  by rw [pcop_hom_apply_ne_zero M p χ (fact.out p.prime).ne_zero, zmod.pcop_p, pcompl_hom.map_one]



/-- The mixed strong homomorphism -/
def pmix_hom : M × pcompl_hom M p →+ strong_map M p :=
  add_monoid_hom.coprod (ppow_hom M p) (pcop_hom M p)

theorem pmix_hom_pair' (pair : M × pcompl_hom M p) :
  pmix_hom M p pair = ppow_hom M p pair.fst + pcop_hom M p pair.snd := rfl

@[simp] theorem pmix_hom_pair (c : M) (χ : pcompl_hom M p) :
  pmix_hom M p (c, χ) = ppow_hom M p c + pcop_hom M p χ := rfl

@[simp] theorem pmix_hom_apply (c : M) (χ : pcompl_hom M p) (n : ℕ) :
  pmix_hom M p (c, χ) n = padic_val_nat p n • c + χ (zmod.pcop_part p n) :=
begin
  rcases eq_or_ne n 0 with rfl | h,
  rw [map_zero, zmod.pcop_zero, pcompl_hom.map_one, add_zero, padic_val_nat.zero, zero_smul],
  rw [pmix_hom_pair, add_apply, ppow_hom_val, pcop_hom_apply_ne_zero M p χ h]
end

end strong_map

end IMO2020N5
end IMOSL
