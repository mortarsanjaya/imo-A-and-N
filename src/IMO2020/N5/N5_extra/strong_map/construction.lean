import IMO2020.N5.N5_extra.strong_map.basic data.zmod.basic number_theory.padics.padic_val

/-!
# Construction of `p`-strong maps

We construct the `p`-strong map structure and also some important examples of `p`-strong maps.
* We define `pcop_domain M p` as the set of maps `χ : additive (zmod p)ˣ →+ M` with `χ(-1) = 0`.
  The set gets its domain name from the fact that it is used as the domain of another map below.
* Given `x : M`, the pure `p`-power strong map `ppow_map M p x`
    is the map `n ↦ ν_p(n) • x` as a `p`-strong map.
  Its corresponding homomorphism is `ppow_hom M p`.
* Given `χ : pcop_domain M p`, the pure `p`-coprime strong map `pcop_map M p χ`
    is the map `n ↦ χ((n / p^ν_p(n)) % p)` as a `p`-strong map.
  Its corresponding homomorphism is `pcop_hom M p`.
* The strong homomorphism `pmix_hom M p` is the coproduct of `ppow_hom M p` and `pcop_hom M p`.
  As a `p`-strong map, it equals `ppow_map M p x + pcop_map M p χ`.

It turns out that `pmix_map M p` is a bijection.
We prove this result and construct the isomorphism in `characterization.lean`.
-/

namespace IMOSL
namespace IMO2020N5

open strong_map



namespace nat

/-- The `p`-coprime part of a positive natural.
  It is defined even for non-prime `p`, but most results assume that `p` is prime. -/
def pcop_part (p n : ℕ) : ℕ := n / p ^ (n.factorization p)

@[simp] lemma pcop_zero (p : ℕ) : pcop_part p 0 = 0 := nat.zero_div _

@[simp] lemma pcop_one (p : ℕ) : pcop_part p 1 = 1 := by simp [pcop_part]

lemma pcop_ne_zero (p : ℕ) {n : ℕ} (h : n ≠ 0) : pcop_part p n ≠ 0 :=
  nat.div_pow_factorization_ne_zero p h

variables {p : ℕ} (hp : p.prime)
include hp

@[simp] lemma pcop_ppow (k : ℕ) : pcop_part p (p ^ k) = 1 :=
  by rw [pcop_part, nat.prime.factorization_pow hp,
         finsupp.single_eq_same, nat.div_self (pow_pos hp.pos k)]
  
@[simp] lemma pcop_p : pcop_part p p = 1 :=
  by rw [pcop_part, nat.prime.factorization_self hp, pow_one, nat.div_self hp.pos]

lemma not_dvd_p_pcop {n : ℕ} (hn : n ≠ 0) : ¬p ∣ pcop_part p n :=
  nat.not_dvd_div_pow_factorization hp hn

lemma coprime_p_pcop {n : ℕ} (hn : n ≠ 0) : p.coprime (pcop_part p n) :=
  nat.coprime_of_div_pow_factorization hp hn

lemma eq_pcop_of_coprime {n : ℕ} (hn : n ≠ 0) (h : p.coprime n) : pcop_part p n = n :=
begin
  rw [pcop_part, (nat.factorization_eq_zero_iff' n p).mpr, pow_zero, nat.div_one],
  right; left; rwa ← hp.coprime_iff_not_dvd
end

lemma eq_mul_ppow_pcop (n : ℕ) : p ^ (n.factorization p) * pcop_part p n = n :=
  nat.mul_div_cancel' (nat.pow_factorization_dvd n p)

theorem pcop_mul (m n : ℕ) : pcop_part p (m * n) = pcop_part p m * pcop_part p n :=
begin
  rcases eq_or_ne m 0 with rfl | hm,
  rw [zero_mul, pcop_zero p, zero_mul],
  rcases eq_or_ne n 0 with rfl | hn,
  rw [mul_zero, pcop_zero p, mul_zero],
  dsimp only [pcop_part],
  rw [nat.factorization_mul hm hn, finsupp.coe_add,
      pi.add_apply, pow_add, nat.mul_div_mul_comm_of_dvd_dvd],
  all_goals { refine nat.pow_factorization_dvd _ p }
end

end nat



namespace zmod

variables (p : ℕ) [fact (p.prime)]

/-- The `p`-coprime part of a positive natural, embedded into `(zmod p)ˣ`.
  If `n = 0`, we define the `p`-coprime part to be `1` in `(zmod p)ˣ`. -/
def pcop_part (n : ℕ) : (zmod p)ˣ :=
  dite (n = 0) (λ _, 1) (λ h : n ≠ 0, zmod.unit_of_coprime (nat.pcop_part p n)
    (nat.coprime_comm.mp (nat.coprime_p_pcop (fact.out p.prime) h)))

@[simp] lemma pcop_zero : pcop_part p 0 = 1 :=
  by rw [pcop_part, dif_pos rfl]

@[simp] lemma pcop_one : pcop_part p 1 = 1 :=
  by simp only [pcop_part, dif_neg (one_ne_zero : 1 ≠ 0),
    zmod.unit_of_coprime, nat.pcop_one, nat.cast_one, inv_one]; refl

@[simp] lemma pcop_ppow (k : ℕ) : pcop_part p (p ^ k) = 1 :=
  let h := fact.out p.prime in by simp only [pcop_part, dif_neg (pow_ne_zero k h.ne_zero),
    nat.pcop_ppow h, zmod.unit_of_coprime, nat.cast_one, inv_one]; refl
  
@[simp] lemma pcop_p : pcop_part p p = 1 :=
  let h := fact.out p.prime in by simp only [pcop_part, dif_neg h.ne_zero,
    nat.pcop_p h, zmod.unit_of_coprime, nat.cast_one, inv_one]; refl

@[simp] lemma pcop_val {n : ℕ} (h : n ≠ 0) :
  (zmod.pcop_part p n : zmod p).val = nat.pcop_part p n % p :=
  by rw [zmod.pcop_part, dif_neg h, zmod.coe_unit_of_coprime, zmod.val_nat_cast]

theorem pcop_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
  pcop_part p (m * n) = pcop_part p m * pcop_part p n :=
begin
  rw ← units.eq_iff,
  simp only [pcop_part, zmod.unit_of_coprime, units.coe_mul],
  rw [dif_neg hm, dif_neg hn, dif_neg (mul_ne_zero hm hn)],
  simp only [units.coe_mk],
  rw [nat.pcop_mul (fact.out p.prime), nat.cast_mul]
end

end zmod



section extra_lemmas

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

lemma nat_pcop_part_add_eq_p_pow : p ∣ nat.pcop_part p a + nat.pcop_part p b :=
begin
  dsimp only [nat.pcop_part],
  let h0 : ∀ n : ℕ, n.factorization p = padic_val_nat p n :=
    λ n, nat.factorization_def n (fact.out p.prime),
  rw [h0, padic_add_eq_p_pow p ha hb h, ← h0, ← nat.add_div_of_dvd_left, h, h0],
  clear h0,  
  work_on_goal 2 { exact nat.pow_factorization_dvd b p },
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

end extra_lemmas







namespace strong_map

/-- The type of maps `χ : additive (zmod p)ˣ →+ M` for which `χ(-1) = 0` -/
@[ancestor strong_map]
structure pcop_domain (M : Type*) [add_comm_monoid M] (p : ℕ) extends additive (zmod p)ˣ →+ M :=
  (map_neg_one' : to_fun (additive.of_mul (-1)) = 0)



namespace pcop_domain

variables {M : Type*} [add_comm_monoid M] {p : ℕ}

/-- Instead of coercing to `additive (zmod p)ˣ → M`,
  we coerce to `(zmod p)ˣ → M` for an *unknown* reason. -/
instance : has_coe_to_fun (pcop_domain M p) (λ (_ : pcop_domain M p), (zmod p)ˣ → M) :=
  ⟨λ f, (pcop_domain.to_add_monoid_hom f).to_fun⟩

@[simp] theorem to_fun_eq_coe (f : pcop_domain M p) : f.to_fun = f := rfl

@[simp] theorem map_one (f : pcop_domain M p) : f 1 = 0 := f.map_zero'

@[simp] theorem map_mul_add (f : pcop_domain M p) {x y : (zmod p)ˣ} : f (x * y) = f x + f y :=
  f.map_add' x y

@[simp] theorem map_neg_one (f : pcop_domain M p) : f (-1) = 0 := f.map_neg_one'

@[simp] theorem map_additive (f : pcop_domain M p) {x : (zmod p)ˣ} :
  f (additive.of_mul x) = f x := rfl

instance fun_like {M : out_param Type*} [add_comm_monoid M] {p : ℕ} :
  fun_like (pcop_domain M p) (zmod p)ˣ (λ _, M) :=
  ⟨(λ f, f.to_fun), (λ f g h, by cases f; cases g; simp at h; congr')⟩

instance has_coe_add_monoid_hom : has_coe (pcop_domain M p) (additive (zmod p)ˣ →+ M) :=
  ⟨pcop_domain.to_add_monoid_hom⟩

@[simp, norm_cast] lemma coe_add_monoid_hom (f : pcop_domain M p) :
  ⇑(f : additive (zmod p)ˣ →+ M) = f := rfl

theorem coe_inj {f g : pcop_domain M p} : (f : additive (zmod p)ˣ → M) = g ↔ f = g :=
  ⟨(λ h, fun_like.coe_injective h), (λ h, by rw h)⟩

@[ext] theorem ext {f g : pcop_domain M p} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

theorem ext_iff {f g : pcop_domain M p} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, by rw h, ext⟩

instance : has_zero (pcop_domain M p) :=
  ⟨⟨0, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.zero_apply]⟩⟩

@[simp] theorem zero_apply {x : (zmod p)ˣ} : (0 : pcop_domain M p) x = 0 := rfl

instance : has_add (pcop_domain M p) :=
  ⟨λ f g, ⟨f + g, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply];
    simp only [coe_add_monoid_hom, map_additive, map_neg_one, add_zero]⟩⟩

@[simp] theorem add_apply {f g : pcop_domain M p} {x : (zmod p)ˣ} : (f + g) x = f x + g x := rfl

instance : add_comm_monoid (pcop_domain M p) :=
{ add_comm := λ f g, by ext; rw [add_apply, add_apply, add_comm],
  add_assoc := λ f g h, by ext; simp only [add_apply]; rw add_assoc,
  zero_add := λ f, by ext; rw [add_apply, zero_apply, zero_add],
  add_zero := λ f, by ext; rw [add_apply, zero_apply, add_zero],
  .. pcop_domain.has_zero, .. pcop_domain.has_add }

@[simp] theorem nsmul_apply (n : ℕ) (f : pcop_domain M p) (x : (zmod p)ˣ) : (n • f) x = n • f x :=
begin
  induction n with n n_ih,
  rw [zero_smul, zero_smul, zero_apply],
  rw [nat.succ_eq_add_one, add_smul, one_smul, add_smul, one_smul, add_apply, n_ih]
end

end pcop_domain



variables (M : Type*) [add_comm_monoid M] (p : ℕ) [fact p.prime]

/-- The pure `p`-power strong map -/
def ppow_map (x : M) : strong_map M p :=
{ to_fun := λ n, padic_val_nat p n • x,
  map_zero' := by rw [padic_val_nat.zero, zero_smul],
  map_mul_add' := λ x y hx hy, by rw [padic_val_nat.mul p hx hy, add_smul],
  strong' := λ k a b ha hb h, by simp only []; rw padic_add_eq_p_pow p ha hb h }

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
def pcop_map (χ : pcop_domain M p) : strong_map M p :=
{ to_fun := λ n, ite (n = 0) 0 (χ (zmod.pcop_part p n)),
  map_zero' := rfl,
  map_mul_add' := λ x y hx hy, by rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy),
    zmod.pcop_mul p hx hy, pcop_domain.map_mul_add χ],
  strong' := λ k a b ha hb h, by simp only []; rw [if_neg ha, if_neg hb,
    ← zmod_pcop_part_add_eq_p_pow p ha hb h, ← neg_one_mul, pcop_domain.map_mul_add,
    pcop_domain.map_neg_one, zero_add] }

@[simp] theorem pcop_map_val (χ : pcop_domain M p) (n : ℕ) :
  pcop_map M p χ n = ite (n = 0) 0 (χ (zmod.pcop_part p n)) := rfl

@[simp] theorem pcop_map_zero : pcop_map M p 0 = 0 :=
  by ext; simp only [pcop_map_val, zero_apply, pcop_domain.zero_apply, if_t_t]

@[simp] theorem pcop_map_apply_zero (χ : pcop_domain M p) : pcop_map M p χ 0 = 0 := rfl

@[simp] theorem pcop_map_apply_ne_zero (χ : pcop_domain M p) {n : ℕ} (h : n ≠ 0) :
  pcop_map M p χ n = χ (zmod.pcop_part p n) :=
  by rw [pcop_map_val, if_neg h]

@[simp] theorem pcop_map_ppow (χ : pcop_domain M p) (k : ℕ) : pcop_map M p χ (p ^ k) = 0 :=
  by rw [pcop_map_apply_ne_zero M p χ (pow_ne_zero _ (fact.out p.prime).ne_zero),
         zmod.pcop_ppow, pcop_domain.map_one]

@[simp] theorem pcop_map_p (χ : pcop_domain M p) : pcop_map M p χ p = 0 :=
  by rw [pcop_map_apply_ne_zero M p χ (fact.out p.prime).ne_zero, zmod.pcop_p, pcop_domain.map_one]

@[simp] theorem pcop_map_add (χ φ : pcop_domain M p) :
  pcop_map M p (χ + φ) = pcop_map M p χ + pcop_map M p φ :=
begin
  ext x; rcases eq_or_ne x 0 with rfl | h,
  rw [add_apply, pcop_map_apply_zero, pcop_map_apply_zero, pcop_map_apply_zero, zero_add],
  rw add_apply; repeat { rw pcop_map_apply_ne_zero M p _ h }; rw pcop_domain.add_apply
end

@[simp] theorem pcop_map_nsmul (n : ℕ) (χ : pcop_domain M p) :
  pcop_map M p (n • χ) = n • pcop_map M p χ :=
begin
  ext x; rcases eq_or_ne x 0 with rfl | h,
  rw [pcop_map_apply_zero, smul_def, pcop_map_apply_zero, smul_zero],
  rw smul_def; repeat { rw pcop_map_apply_ne_zero M p _ h }; rw pcop_domain.nsmul_apply
end

theorem pcop_map_inj {χ φ : pcop_domain M p} : pcop_map M p χ = pcop_map M p φ ↔ χ = φ :=
begin
  refine ⟨λ h, _, λ h, by rw h⟩,
  ext n; replace h := fun_like.congr_fun h (n : zmod p).val,
  have h0 := n.ne_zero,
  rw [ne.def, ← zmod.val_eq_zero, ← ne.def] at h0,
  rw [pcop_map_apply_ne_zero M p χ h0, pcop_map_apply_ne_zero M p φ h0] at h,
  suffices : n = zmod.pcop_part p (n : zmod p).val,
    convert h,
  rw [← units.eq_iff, zmod.pcop_part, dif_neg h0],
  have h1 : ((n : zmod p).val : zmod p) = (n : zmod p) :=
    by rw [zmod.nat_cast_val, zmod.cast_id', id.def],
  replace h : p.coprime (n : zmod p).val := by rwa [(fact.out p.prime).coprime_iff_not_dvd,
      ← zmod.nat_coe_zmod_eq_zero_iff_dvd, h1]; exact units.ne_zero n,
  simp only [nat.eq_pcop_of_coprime (fact.out p.prime) h0 h, zmod.coe_unit_of_coprime, h1]
end

/-- The pure `p`-coprime strong map, as a homomorphism -/
def pcop_hom : pcop_domain M p →+ strong_map M p :=
  ⟨pcop_map M p, pcop_map_zero M p, pcop_map_add M p⟩

@[simp] theorem pcop_hom_val (χ : pcop_domain M p) (n : ℕ) :
  pcop_hom M p χ n = ite (n = 0) 0 (χ (zmod.pcop_part p n)) := rfl

theorem pcop_hom_apply_ne_zero (χ : pcop_domain M p) {n : ℕ} (h : n ≠ 0) :
  pcop_hom M p χ n = χ (zmod.pcop_part p n) := by rw [pcop_hom_val, if_neg h]

@[simp] theorem pcop_hom_ppow (χ : pcop_domain M p) (k : ℕ) : pcop_hom M p χ (p ^ k) = 0 :=
  by rw [pcop_hom_apply_ne_zero M p χ (pow_ne_zero k (fact.out p.prime).ne_zero),
         zmod.pcop_ppow, pcop_domain.map_one]

@[simp] theorem pcop_hom_p (χ : pcop_domain M p) : pcop_hom M p χ p = 0 :=
  by rw [pcop_hom_apply_ne_zero M p χ (fact.out p.prime).ne_zero, zmod.pcop_p, pcop_domain.map_one]



/-- The mixed strong homomorphism -/
def pmix_hom : M × pcop_domain M p →+ strong_map M p :=
  add_monoid_hom.coprod (ppow_hom M p) (pcop_hom M p)

theorem pmix_hom_pair' (pair : M × pcop_domain M p) :
  pmix_hom M p pair = ppow_hom M p pair.fst + pcop_hom M p pair.snd := rfl

@[simp] theorem pmix_hom_pair (c : M) (χ : pcop_domain M p) :
  pmix_hom M p (c, χ) = ppow_hom M p c + pcop_hom M p χ := rfl

@[simp] theorem pmix_hom_apply_ne_zero (c : M) (χ : pcop_domain M p) {n : ℕ} (h : n ≠ 0) :
  pmix_hom M p (c, χ) n = padic_val_nat p n • c + χ (zmod.pcop_part p n) :=
  by rw [pmix_hom_pair, add_apply, ppow_hom_val, pcop_hom_apply_ne_zero M p χ h]

end strong_map

end IMO2020N5
end IMOSL
