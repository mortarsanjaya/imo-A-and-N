import IMO2020.N5.N5_extra.strong_map.basic data.zmod.basic number_theory.padics.padic_val

/-!
# Construction of `p`-strong maps

We construct the `p`-strong map structure and also some important examples of `p`-strong maps.
* Given `x : M`, the pure `p`-power strong map `ppow_map M p x` is the map
  `n ↦ ν_p(n) • x` as a `p`-strong map.
  Its corresponding homomorphism is `ppow_hom M p`.
* Given `χ : additive (zmod p)ˣ →+ M` with `χ(-1) = 0`, the pure `p`-coprime strong map
  `pcop_map M p χ` is the map `n ↦ χ((n / p^ν_p(n)) % p)` as a `p`-strong map.
  Its corresponding homomorphism is `pcop_hom M p`.
* Given `(x, χ) : M × (additive (zmod p)ˣ →+ M)` with `χ(-1) = 0`, the mixed strong map
  `pmix_map M p (x, χ)` is the `p`-strong map `ppow_map M p x + pcop_map M p χ`.
  Its corresponding homomorphism is `pmix_hom M p`.

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

variables {p : ℕ} (hp : p.prime)
include hp

@[simp] lemma pcop_p : pcop_part p p = 1 := by dsimp only [pcop_part];
  rw [nat.prime.factorization_self hp, pow_one, nat.div_self hp.pos]

@[simp] lemma pcop_ppow (k : ℕ) : pcop_part p (p ^ k) = 1 := by dsimp only [pcop_part];
  rw [nat.prime.factorization_pow hp, finsupp.single_eq_same, nat.div_self (pow_pos hp.pos k)]

lemma coprime_p_pcop {n : ℕ} (hn : n ≠ 0) : p.coprime (pcop_part p n) :=
  nat.coprime_of_div_pow_factorization hp hn

lemma eq_pcop_of_coprime {n : ℕ} (hn : n ≠ 0) (h : p.coprime n) : pcop_part p n = n :=
begin
  dsimp only [pcop_part],
  rw [(nat.factorization_eq_zero_iff' n p).mpr, pow_zero, nat.div_one],
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

/-- The `p`-coprime part of a positive natural, embedded into `(zmod p)ˣ` -/
def pcop_part (n : ℕ) (h : n ≠ 0) : (zmod p)ˣ :=
  zmod.unit_of_coprime (nat.pcop_part p n)
    (nat.coprime_comm.mp (nat.coprime_p_pcop (fact.out p.prime) h))

@[simp] lemma pcop_one : pcop_part p 1 one_ne_zero = 1 :=
  by simp only [pcop_part, nat.pcop_one, zmod.unit_of_coprime, nat.cast_one, inv_one]; refl

theorem pcop_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
  pcop_part p (m * n) (mul_ne_zero hm hn) = pcop_part p m hm * pcop_part p n hn :=
begin
  rw ← units.eq_iff,
  simp only [pcop_part, zmod.unit_of_coprime, units.coe_mk, units.coe_mul],
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

lemma zmod_pcop_part_add_eq_p_pow : -zmod.pcop_part p a ha = zmod.pcop_part p b hb :=
begin
  rw ← units.eq_iff,
  simp only [zmod.pcop_part, zmod.unit_of_coprime, units.coe_mk, units.coe_neg],
  rw [← add_eq_zero_iff_neg_eq, ← nat.cast_add, zmod.nat_coe_zmod_eq_zero_iff_dvd],
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
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, begin cases f; cases g; simp at h; congr' end }

instance has_coe_add_monoid_hom : has_coe (pcop_domain M p) (additive (zmod p)ˣ →+ M) :=
  ⟨pcop_domain.to_add_monoid_hom⟩

@[simp, norm_cast] lemma coe_add_monoid_hom (f : pcop_domain M p) :
  ⇑(f : additive (zmod p)ˣ →+ M) = f := rfl

theorem coe_inj {f g : pcop_domain M p} : (f : additive (zmod p)ˣ → M) = g ↔ f = g :=
  ⟨(λ h, fun_like.coe_injective h), (λ h, by rw h)⟩

@[ext] theorem ext {f g : pcop_domain M p} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

theorem ext_iff {f g : pcop_domain M p} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, by rw h, ext⟩

instance : has_zero (pcop_domain M p) := ⟨⟨0, by simp⟩⟩

@[simp] theorem zero_apply {x : (zmod p)ˣ} : (0 : pcop_domain M p) x = 0 := rfl

instance : has_add (pcop_domain M p) := ⟨λ f g, ⟨f + g, by simp⟩⟩

@[simp] theorem add_apply {f g : pcop_domain M p} {x : (zmod p)ˣ} : (f + g) x = f x + g x := rfl

instance : add_comm_monoid (pcop_domain M p) :=
{ add_comm := λ f g, by ext; simp only [add_apply, add_comm],
  add_assoc := λ f g h, by ext; simp only [add_apply, add_assoc],
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
def ppow_hom : M →+ strong_map M p :=
{ to_fun := ppow_map M p,
  map_zero' := ppow_map_zero M p,
  map_add' := ppow_map_add M p }

@[simp] theorem ppow_hom_val (x : M) (n : ℕ) : ppow_hom M p x n = padic_val_nat p n • x := rfl

@[simp] theorem ppow_hom_ppow (x : M) (k : ℕ) : ppow_hom M p x (p ^ k) = k • x :=
  by rw [ppow_hom_val, padic_val_nat.prime_pow]

@[simp] theorem ppow_hom_p (x : M) : ppow_hom M p x p = x :=
  by rw [ppow_hom_val, padic_val_nat_self, one_nsmul]







end strong_map

end IMO2020N5
end IMOSL
