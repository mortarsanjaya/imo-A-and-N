import IMO2020.N5.additive_map extra.number_theory.ord_compl_zmod

/-!
# `p`-regular maps

Fix a commutative additive monoid `M` and a prime `p`.
Given `(c, χ) : M × (additive (zmod p)ˣ →+ M)`, the *regular map* `regular_map M p (c, χ)` is the
  additive map given by `p^k t ↦ k • c + χ(t : (zmod p)ˣ)` for any `k ≥ 1` and `t` coprime with `p`.
We will show that map `regular_map M p` is additive and injective with `regular_map M p 0 = 0`.
Then, we construct `regular_hom M p` as a bundled homomorphism version of `regular_map M p`.

We also define the predicate `is_regular_map M p` and prove an equivalent condition:
  an additive map is regular iff `f(t) = f(t % p)` for any `t` coprime with `p`.
Lastly, we prove that `is_regular_map M p f` and `is_regular_map M q f` for `p ≠ q` yields `f = 0`.
-/

namespace IMOSL
namespace IMO2020N5

open extra additive



/-- `p`-regular maps -/
def regular_map (M : Type*) [add_comm_monoid M] (p : ℕ) [fact p.prime]
  (pair : M × (additive (zmod p)ˣ →+ M)) : additive_map M :=
{ to_fun := λ n, ite (n = 0) 0
    (padic_val_nat p n • pair.1 + pair.2 (of_mul (zmod.ord_compl p n))), 
  map_zero' := if_pos rfl,
  map_one' := by rw [if_neg (one_ne_zero : 1 ≠ 0), padic_val_nat.one,
    zero_smul, zero_add, zmod.ord_compl.map_one, of_mul_one, map_zero],
  map_mul' := λ x y hx hy,
    by rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, add_add_add_comm, ← add_smul,
      ← padic_val_nat.mul p hx hy, ← map_add, ← of_mul_mul, zmod.ord_compl.map_mul hx hy] }



namespace regular_map

variables {M : Type*} [add_comm_monoid M] {p : ℕ} [fact p.prime]
  (pair pair' : M × (additive (zmod p)ˣ →+ M))

theorem map_def (n : ℕ) : regular_map M p pair n =
  ite (n = 0) 0 (padic_val_nat p n • pair.1 + pair.2 (of_mul (zmod.ord_compl p n))) := rfl

@[simp] theorem map_zero : regular_map M p pair 0 = 0 := rfl

@[simp] theorem map_ne_zero {n : ℕ} (hn : n ≠ 0) : regular_map M p pair n =
  padic_val_nat p n • pair.1 + pair.2 (of_mul (zmod.ord_compl p n)) := if_neg hn

@[simp] theorem map_one : regular_map M p pair 1 = 0 :=
  additive_map.map_one (regular_map M p pair)

@[simp] theorem map_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
  regular_map M p pair (m * n) = regular_map M p pair m + regular_map M p pair n :=
  additive_map.map_mul (regular_map M p pair) hm hn

@[simp] theorem map_pow (m k : ℕ) :
  regular_map M p pair (m ^ k) = k • regular_map M p pair m :=
  additive_map.map_pow (regular_map M p pair) m k

theorem map_p : regular_map M p pair p = pair.1 :=
  by rw [map_ne_zero pair (fact.out p.prime).ne_zero, padic_val_nat_self, one_nsmul,
         zmod.ord_compl.map_self, of_mul_one, add_monoid_hom.map_zero, add_zero]

theorem map_coprime {t : ℕ} (h : t.coprime p) :
  regular_map M p pair t = pair.2 (of_mul (zmod.unit_of_coprime t h)) :=
begin
  have h0 : ¬p ∣ t := by rwa [← nat.prime.coprime_iff_not_dvd (fact.out p.prime), nat.coprime_comm],
  rw [map_ne_zero, padic_val_nat.eq_zero_of_not_dvd h0,
      zero_smul, zero_add, zmod.ord_compl.map_coprime h],
  rintros rfl; exact h0 (dvd_zero p)
end

theorem map_coprime_mod_p_eq {t : ℕ} (h : t.coprime p) :
  regular_map M p pair t = regular_map M p pair (t % p) :=
begin
  have h0 : ∀ n : ℕ, n.coprime p ↔ ¬p ∣ n := λ n,
    by rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd (fact.out p.prime)],
  replace h0 : (t % p).coprime p :=
    by rwa [h0, ← nat.div_add_mod t p, ← nat.dvd_add_iff_right ⟨_, rfl⟩, ← h0] at h,
  rw [map_coprime pair h, map_coprime pair h0]; congr' 2,
  rw [units.ext_iff, zmod.coe_unit_of_coprime, zmod.coe_unit_of_coprime, zmod.nat_cast_mod]
end



theorem map_pair_add : regular_map M p (pair + pair') = regular_map M p pair + regular_map M p pair' :=
begin
  ext x; rcases eq_or_ne x 0 with rfl | h,
  rw [additive_map.map_zero, additive_map.map_zero],
  rw [map_ne_zero _ h, additive_map.add_apply, map_ne_zero _ h, map_ne_zero _ h,
      add_add_add_comm, ← add_monoid_hom.add_apply, ← smul_add, prod.fst_add, prod.snd_add]
end

theorem map_pair_zero : regular_map M p 0 = 0 :=
  by ext x; rw [map_def, prod.fst_zero, smul_zero, zero_add, prod.snd_zero,
                add_monoid_hom.zero_apply, additive_map.zero_apply, if_t_t]

theorem injective : function.injective (regular_map M p) :=
begin
  rintros ⟨c, χ⟩ ⟨d, ρ⟩ h,
  rw fun_like.ext_iff at h,
  rw prod.mk.inj_iff; split,
  replace h := h p; rwa [map_p, map_p] at h,
  ext x,
  have h0 := zmod.val_coe_unit_coprime (to_mul x),
  have h1 : zmod.unit_of_coprime (to_mul x : zmod p).val h0 = to_mul x :=
    by rw [units.ext_iff, zmod.coe_unit_of_coprime, zmod.nat_cast_val, zmod.cast_id', id.def],
  replace h := h (to_mul x : zmod p).val,
  rwa [map_coprime (c, χ) h0, map_coprime (d, ρ) h0, h1, of_mul_to_mul] at h
end

theorem inj : regular_map M p pair = regular_map M p pair' ↔ pair = pair' :=
  ⟨λ h, injective h, congr_arg _⟩

end regular_map



open regular_map

/-- `p`-regular mapping as a homomorphism -/
def regular_hom (M : Type*) [add_comm_monoid M] (p : ℕ) [fact p.prime] : 
  M × (additive (zmod p)ˣ →+ M) →+ additive_map M :=
⟨regular_map M p, map_pair_zero, map_pair_add⟩

/-- `p`-regularity predicate -/
def is_regular_map (M : Type*) [add_comm_monoid M] (p : ℕ) [fact p.prime] (f : additive_map M) :=
  ∃ pair : M × (additive (zmod p)ˣ →+ M), f = regular_map M p pair



namespace is_regular_map

variables {M : Type*} [add_comm_monoid M] {p q : ℕ} [fact p.prime] [fact q.prime]

/-- The zero additive map is `p`-regular -/
theorem zero : is_regular_map M p 0 := ⟨0, map_pair_zero.symm⟩

/-- An equivalent condition for `p`-regularity -/
theorem iff (f : additive_map M) : is_regular_map M p f ↔ ∀ t : ℕ, t.coprime p → f t = f (t % p) :=
begin
  have hp := fact.out p.prime,
  refine ⟨λ h t h0, _, λ h, ⟨⟨f p, ⟨λ x, f (to_mul x : zmod p).val, _, λ x y, _⟩⟩, _⟩⟩,
  rcases h with ⟨pair, rfl⟩; exact map_coprime_mod_p_eq pair h0,
  rw [to_mul_zero, units.coe_one, zmod.val_one, additive_map.map_one],
  { have h0 : ∀ u : additive (zmod p)ˣ, (to_mul u : zmod p).val.coprime p :=
      λ u, zmod.val_coe_unit_coprime (to_mul u),
    suffices : ∀ x : ℕ, x.coprime p → x ≠ 0,
      rw [to_mul_add, units.coe_mul, zmod.val_mul, ← h _ (nat.coprime.mul (h0 x) (h0 y)),
          additive_map.map_mul _ (this _ (h0 x)) (this _ (h0 y))],
    rintros x h1 rfl,
    rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd hp] at h1,
    exact h1 (dvd_zero p) },
  { ext n; rcases eq_or_ne n 0 with rfl | h0,
    rw [additive_map.map_zero, regular_map.map_zero],
    rw regular_map.map_ne_zero _ h0; simp only [],
    nth_rewrite 0 ← nat.ord_proj_mul_ord_compl_eq_self n p,
    rw [additive_map.map_mul f (pow_ne_zero _ hp.ne_zero) (ne_of_gt (p.ord_compl_pos h0)),
        additive_map.map_pow, add_monoid_hom.coe_mk, to_mul_of_mul, ← nat.factorization_def _ hp,
        zmod.ord_compl.map_ne_zero_val h0, ← h],
    rw nat.coprime_comm; exact nat.coprime_ord_compl hp h0 }
end

/-- Condition for two `p`-regular maps to be equal -/
theorem ext_iff_at_le_p {f g : additive_map M} (hf : is_regular_map M p f)
  (hg : is_regular_map M p g) : f = g ↔ ∀ k : ℕ, 0 < k → k ≤ p → f k = g k :=
begin
  refine ⟨λ h k _ _, by rw h, λ h, _⟩,
  ext n; rcases eq_or_ne n 0 with rfl | h0,
  rw [additive_map.map_zero, additive_map.map_zero],
  have hp := fact.out p.prime,
  have h1 : ord_proj[p] n ≠ 0 := pow_ne_zero _ hp.ne_zero,
  have h2 : ord_compl[p] n ≠ 0 := ne_of_gt (nat.ord_compl_pos p h0),
  rw [← nat.ord_proj_mul_ord_compl_eq_self n p, additive_map.map_mul f h1 h2,
      additive_map.map_pow, additive_map.map_mul g h1 h2, additive_map.map_pow],
  rw iff at hf hg,
  have h3 : (ord_compl[p] n).coprime p := nat.coprime.symm (nat.coprime_ord_compl hp h0),
  rw [hf _ h3, hg _ h3, h _ hp.pos (le_refl p), h _ _ (le_of_lt (nat.mod_lt _ hp.pos))],
  rwa [zero_lt_iff, ne.def, ← nat.dvd_iff_mod_eq_zero, ← hp.coprime_iff_not_dvd, nat.coprime_comm]
end

/-- Condition for a `p`-regular map to be zero -/
theorem zero_iff_at_le_p {f : additive_map M} (hf : is_regular_map M p f) :
  f = 0 ↔ ∀ k : ℕ, 0 < k → k ≤ p → f k = 0 :=
  by rw ext_iff_at_le_p hf zero; simp only [additive_map.zero_apply]

/-- (Private) small lemma for values of `p`-regular map at two `nat` congruent modulo `p` -/
private lemma map_modeq_coprime {f : additive_map M} (hf : is_regular_map M p f)
  {m n : ℕ} (h : m % p = n % p) (h0 : n.coprime p) : f m = f n :=
begin
  rw iff at hf,
  rw [hf n h0, ← h, ← hf],
  unfold nat.coprime at h0 ⊢,
  rw ← nat.modeq at h,
  rw [nat.modeq.gcd_eq_of_modeq h, h0]
end

/-- Distinction between `p`-regular and `q`-regular for `p ≠ q` -/
theorem distinction {f : additive_map M} (hpf : is_regular_map M p f) (hqf : is_regular_map M q f)
  (h : p ≠ q) : f = 0 :=
begin
  rw ne_iff_lt_or_gt at h,
  unfreezingI { wlog : p < q := h using [p q, q p] },
  work_on_goal 2 { exact this hqf hpf },
  have hp := fact.out p.prime,
  have hq := fact.out q.prime,
  have hpq := (nat.coprime_primes hp hq).mpr (ne_of_lt h),

  rw zero_iff_at_le_p hpf,
  suffices : ∃ c : M, f p + c = 0,
  { cases this with c h0,
    replace hpf : ∀ k : ℕ, f (q + k * p) = f q :=
      λ k, map_modeq_coprime hpf (by rw nat.add_mul_mod_self_right) hpq.symm,
    suffices : ∀ k : ℕ, 0 < k → k ≤ p → f q = f k + f p,
    { intros k h1 h2,
      rw [← add_zero (f k), ← h0, ← add_assoc, ← this k h1 h2,
          this 1 one_pos (le_of_lt hp.one_lt), additive_map.map_one, zero_add] },
    intros k h1 h2,
    rw [← hpf k, ← additive_map.map_mul f (ne_of_gt h1) hp.ne_zero],
    apply map_modeq_coprime hqf,
    rw nat.add_mod_left,
    refine nat.coprime.mul _ hpq,
    rw [nat.coprime_comm, hq.coprime_iff_not_dvd],
    exact nat.not_dvd_of_pos_of_lt h1 (lt_of_le_of_lt h2 h) },
  
  obtain ⟨n, h0⟩ := nat.exists_mul_mod_eq_one_of_coprime hpq hq.one_lt,
  use f n,
  rw ← nat.mod_eq_of_lt hq.one_lt at h0,
  rw [← additive_map.map_mul f hp.ne_zero, map_modeq_coprime hqf h0 q.coprime_one_left],
  exact f.map_one,
  rintros rfl,
  rw [mul_zero, nat.zero_mod, nat.mod_eq_of_lt hq.one_lt] at h0,
  revert h0; exact zero_ne_one
end

end is_regular_map

end IMO2020N5
end IMOSL
