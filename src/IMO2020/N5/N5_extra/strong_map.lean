import IMO2020.N5.N5_extra.good_map data.nat.log data.nat.modeq data.zmod.basic

/-!
# `p`-strong maps

We characterize `p`-strong maps.
As it turns out, they are precisely the functions that can be described as
  `p^k t ↦ kc + χ(t mod p)` for some `c : M` and `χ : (zmod p)ˣ → M` where
  `χ` is a map with `χ(ab) = χ(a) χ(b)` for any `a b : (zmod p)ˣ` and `χ(-1) = 1`.
Alternatively, using a bijection `(zmod (p / 2)) → additive (zmod p)ˣ/⟨-1⟩`
  for odd `p`, we can replace `χ` with a map `(zmod (p / 2)) →+ M`.

TODO: Do the constructions!
1. Construct the "natural" `p`-strong map `M →+ additive_map M`.
We will call it the `p`-type map.
[DONE]

2. Construct the homomorphism `(zmod (p / 2)) → additive (zmod p)ˣ/⟨-1⟩` for `p` odd.
3. Construct the `p`-strong map `((zmod (p / 2)) →+ M) →+ additive_map M`.
We will call it the `coprime`-type map.
4. Construct the `p`-strong map `(M × ((zmod (p / 2) →+ M)) →+ additive_map M`.
The map is obtained by combining a `p`-type and `coprime`-type map.
4. Construct the type `strong_map M p` of `p`-strong elements of `additive_map M`.
5. Construct the bijection between `strong_map M p` and `M × (zmod (p / 2)`.
-/

namespace IMOSL
namespace IMO2020N5

open additive_map
open_locale classical



section constructions


/-
section coprime_part_zmod

variables {p : ℕ} (hp : p.prime)
include hp

private def coprime_part_zmod {n : ℕ} (h : n ≠ 0) : (zmod p)ˣ :=
  zmod.unit_of_coprime (n / p ^ (n.factorization p))
  (by rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd hp];
    exact nat.not_dvd_div_pow_factorization hp h)

private lemma coprime_part_zmod_mul {a : ℕ} (h : a ≠ 0) {b : ℕ} (h0 : b ≠ 0) :
  coprime_part_zmod hp (mul_ne_zero h h0) = coprime_part_zmod hp h * coprime_part_zmod hp h0 :=
begin
  unfold coprime_part_zmod,
  
end

end coprime_part_zmod
-/



variables {M : Type*} [add_cancel_comm_monoid M] (p : ℕ) [fact (p.prime)]

/-- The pure `p`-type additive map -/
def pstrong_pure_p_fun (c : M) : additive_map M :=
{ to_fun := λ n, padic_val_nat p n • c,
  map_zero' := by rw [padic_val_nat.zero, zero_smul],
  map_mul_add' := λ x y hx hy, by rw [padic_val_nat.mul p (ne_of_gt hx) (ne_of_gt hy), add_smul] }

@[simp] theorem pstrong_pure_p_zero : pstrong_pure_p_fun p (0 : M) = 0 :=
  by ext; rw ← to_fun_eq_coe; simp only [pstrong_pure_p_fun, smul_zero, zero_apply]

@[simp] theorem pstrong_pure_p_add (a b : M) :
  pstrong_pure_p_fun p (a + b) = pstrong_pure_p_fun p a + pstrong_pure_p_fun p b :=
  by ext; rw add_apply; repeat { rw ← to_fun_eq_coe }; simp only [pstrong_pure_p_fun, smul_add]

theorem pstrong_pure_p_pstrong (c : M) : strong (fact.out p.prime) (pstrong_pure_p_fun p c) :=
begin
  intros k a b ha hb h,
  rw ← to_fun_eq_coe; dsimp only [pstrong_pure_p_fun],
  congr' 1; clear c,
  sorry
end

/-- The above map as `M →+ additive_map M` -/
def pstrong_pure_p_hom : M →+ additive_map M :=
{ to_fun := pstrong_pure_p_fun p,
  map_zero' := pstrong_pure_p_zero p,
  map_add' := pstrong_pure_p_add p }




/-
/-- The pure `coprime`-part, coming from `χ : additive (zmod p)ˣ →+ M` with `χ(-1) = 0` -/
def pstrong_pure_coprime_mul (χ : additive (zmod p)ˣ →+ M) (h : χ (additive.of_mul (-1)) = 0) :
  additive_map M :=
{ to_fun := λ n, dite (n = 0) (λ _, 0)
    (λ hn0 : n ≠ 0, χ (additive.of_mul (coprime_part_zmod p hn0))),
  map_zero' := by rw dif_pos; refl,
  map_mul_add' := λ x y hx hy, begin
    rw [dif_neg (ne_of_gt (mul_pos hx hy)), dif_neg (ne_of_gt hx), dif_neg (ne_of_gt hy)],
    
  end
}
-/

/-
def pstrong_pure_coprime (χ : zmod (p / 2) →+ M) : additive_map M :=
{ to_fun := λ n, dite (n = 0) (λ _, 0) (λ h : n ≠ 0, )

}
-/

end constructions



section results

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} (hp : p.prime) (f : additive_map M)
include hp

private lemma pstrong_mod_p_induct {a : ℕ} (h : good (p ^ a) f)
  {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) (h0 : k < p ^ a) : f k = f (k % p) :=
begin
  rcases a.eq_zero_or_pos with rfl | h1,
  rw [pow_zero, nat.lt_one_iff] at h0,
  rw [h0, nat.zero_mod],
  revert hkp h0 k h; refine nat.le_induction _ _ a h1; clear h1 a,
  rw pow_one; intros h k hkp h0,
  rw nat.mod_eq_of_lt h0,
  intros n hn1 n_ih h k h0 h1,
  induction k using nat.strong_induction_on with k k_ih,
  cases lt_or_le k (p ^ n) with h2 h2,
  exact n_ih (good_factor f (pow_pos hp.pos _) h ⟨p, pow_succ' p n⟩) h0 h2,
  clear n_ih,

  let c := p ^ (n + 1) / k,
  let d := p ^ (n + 1) % k,
  have X : ∀ a b : ℕ, 0 < b % a ↔ ¬a ∣ b :=
    λ a b, by rw [zero_lt_iff, ne.def, nat.dvd_iff_mod_eq_zero],
  have kpos : 0 < k := by rw zero_lt_iff; rintros rfl; exact h0 ⟨0, by rw mul_zero⟩,
  have cpos : 0 < c := nat.div_pos (le_of_lt h1) kpos,
  have dpos : 0 < d := begin
    rw [X, nat.dvd_prime_pow hp],
    rintros ⟨t, ht, rfl⟩,
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
    rwa [nat.div_lt_iff_lt_mul kpos, pow_succ, mul_lt_mul_left hp.pos]
  end,
  have h3 : c * k + d = p ^ (n + 1) := nat.div_add_mod' _ k,
  rw [← add_right_inj (f c), ← map_mul_add f cpos kpos, h _ _ (mul_pos cpos kpos) dpos h3],
  replace h3 : p ∣ d + c * k := ⟨p ^ n, by rw [add_comm, h3, pow_succ]⟩,
  have h4 : ¬p ∣ c := nat.not_dvd_of_pos_of_lt cpos h2,
  have h5 := nat.prime.not_dvd_mul hp h4 h0,
  have h6 : ¬p ∣ d := λ h6, by rw nat.dvd_add_right h6 at h3; exact h5 h3,
  have h7 : d < k := (p ^ (n + 1)).mod_lt kpos,
  replace k_ih := k_ih d h7 h6 (lt_trans h7 h1),
  replace h : good p f := good_factor f (pow_pos hp.pos _) h ⟨p ^ n, by rw pow_succ⟩,
  rw [k_ih, ← nat.mod_eq_of_lt h2, ← good_prime_mul_mod_p f hp h h4 h0,
      h (c * k % p) (d % p) (by rwa X) (by rwa X)],
  rw [add_comm, ← nat.add_mod_add_of_le_add_mod, nat.mod_eq_zero_of_dvd h3, zero_add],
  exact nat.le_mod_add_mod_of_dvd_add_of_not_dvd h3 h6
end

theorem pstrong_mod_p (h : strong hp f) {k : ℕ} (hkp : ¬(p : ℕ) ∣ k) : f k = f (k % p) :=
  pstrong_mod_p_induct hp f (h k) hkp (nat.lt_pow_self hp.one_lt k)

end results



end IMO2020N5
end IMOSL
