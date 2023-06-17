import field_theory.finite.basic

/-! # IMO 2006 N5 -/

namespace IMOSL
namespace IMO2006N5

open finset

def good (x y : ℤ) (p : ℕ) := (range p).sum (λ i, x ^ i) = y ^ (p - 2) - 1



lemma prime_geom_sum_zero_mod_imp_of_prime {p : ℕ} (hp : p.prime) {q : ℕ} [fact q.prime]
  {x : zmod q} (h : (range p).sum (λ i, x ^ i) = 0) : (q : zmod p) = 1 ∨ q = p :=
let h0 := (geom_sum_mul x p).symm.trans (mul_eq_zero_of_left h _) in
(eq_or_ne x 0).elim
  (λ h1, by rw [h1, zero_pow hp.pos, sub_eq_zero] at h0; exact absurd h0 zero_ne_one)
  (λ h1, (hp.eq_one_or_self_of_dvd _ $ order_of_dvd_of_pow_eq_one $ eq_of_sub_eq_zero h0).symm.imp
    (λ h2, by replace h1 := zmod.order_of_dvd_card_sub_one h1;
      rwa [h2, ← zmod.nat_coe_zmod_eq_zero_iff_dvd,
        nat.cast_sub _inst_1.out.pos, nat.cast_one, sub_eq_zero] at h1)
    (λ h2, begin
      conv at h { congr, congr, skip, funext, rw [order_of_eq_one_iff.mp h2, one_pow] },
      rw [sum_const, card_range, nsmul_one, zmod.nat_coe_zmod_eq_zero_iff_dvd] at h,
      exact (nat.prime_dvd_prime_iff_eq _inst_1.out hp).mp h
    end))

lemma dvd_prime_geom_sum_imp_of_prime {p : ℕ} (hp : p.prime) {q : ℕ} (hq : q.prime)
  {x : ℤ} (h : (q : ℤ) ∣ (range p).sum (λ i, x ^ i)) : (q : zmod p) = 1 ∨ q = p :=
@prime_geom_sum_zero_mod_imp_of_prime p hp q ⟨hq⟩ x $
  by rwa [sum_congr rfl (λ i _, (x.cast_pow i).symm),
    ← int.cast_sum, zmod.int_coe_zmod_eq_zero_iff_dvd]

lemma zmod_eq_one_of_prime_factors_zmod_eq_one {d c : ℕ} :
  (∀ q : ℕ, q.prime → q ∣ c → (q : zmod d) = 1) → (c : zmod d) = 1 :=
nat.rec_on_mul
  (λ h, nat.cast_zero.trans $ add_left_cancel $ (add_zero 1).trans $
    (h 2 nat.prime_two $ dvd_zero 2).symm.trans nat.cast_two)
  (λ _, nat.cast_one)
  (λ p h h0, h0 p h $ dvd_refl p)
  (λ a b h h0 h1, (nat.cast_mul a b).trans $ (congr_arg2 has_mul.mul
    (h $ λ q h2 h3, h1 q h2 $ dvd_mul_of_dvd_left h3 b)
    (h0 $ λ q h2 h3, h1 q h2 $ dvd_mul_of_dvd_right h3 a)).trans $ mul_one 1) c

lemma nat_dvd_prime_geom_sum_imp {p : ℕ} (hp : p.prime) {d : ℕ} {x : ℤ}
  (h : (d : ℤ) ∣ (range p).sum (λ i, x ^ i)) : (d : zmod p) = 1 ∨ p ∣ d :=
or_iff_not_imp_right.mpr $ λ h0, zmod_eq_one_of_prime_factors_zmod_eq_one $
  λ q h1 h2, (dvd_prime_geom_sum_imp_of_prime hp h1 $
    (int.coe_nat_dvd.mpr h2).trans h).resolve_right $
      λ h3, h0 $ (dvd_of_eq h3.symm).trans h2

lemma int_nonneg_dvd_prime_geom_sum_imp {p : ℕ} (hp : p.prime) {d : ℤ} (h : 0 ≤ d)
  {x : ℤ} (h0 : d ∣ (range p).sum (λ i, x ^ i)) : (d : zmod p) = 1 ∨ (d : zmod p) = 0 :=
begin
  rcases int.eq_coe_of_zero_le h with ⟨d, rfl⟩,
  rw [int.cast_coe_nat, zmod.nat_coe_zmod_eq_zero_iff_dvd],
  exact nat_dvd_prime_geom_sum_imp hp h0
end

/-- We only need this result for `p` odd, although it obviously holds for `p = 2`. -/
lemma p_odd_geom_sum_mod_p {p : ℕ} (hp : p.prime) (h : odd p) (x : ℤ) :
  let N := (((range p).sum (λ i, x ^ i) : ℤ) : zmod p) in N = 1 ∨ N = 0 :=
  int_nonneg_dvd_prime_geom_sum_imp hp (le_of_lt h.geom_sum_pos) (dvd_refl _)







/-! # Start of the solution -/
lemma p_eq_2_good_iff (x y : ℤ) : good x y 2 ↔ x = -1 :=
  by rwa [good, nat.sub_self, pow_zero, sub_self, geom_sum_two, add_eq_zero_iff_eq_neg]

lemma p_eq_3_good_iff (x y : ℤ) : good x y 3 ↔ y = x ^ 2 + x + 2 :=
  by rwa [good, geom_sum_succ', geom_sum_two, bit1, nat.add_sub_cancel_left,
    pow_one, eq_sub_iff_add_eq, ← add_assoc, add_assoc, ← bit0, eq_comm]

/-- Slow! (0.7s-0.8s) -/
lemma p_eq_3_of_good_odd {x y : ℤ} {p : ℕ}
  (h : p.prime) (h0 : odd p) (h1 : good x y p) : p = 3 :=
begin
  ---- Preliminary
  rw [good, ← geom_sum_mul] at h1,
  let A : ℤ := (range (p - 2)).sum (λ i, y ^ i),
  have h2 : 0 ≤ A := le_of_lt (nat.odd.sub_even h.two_le h0 even_two).geom_sum_pos,
  have h3 : 0 < y - 1 := pos_of_mul_pos_right (lt_of_lt_of_eq h0.geom_sum_pos h1) h2,
  replace h1 : ∀ d : ℤ, 0 ≤ d → d ∣ A * (y - 1) → (d : zmod p) = 1 ∨ (d : zmod p) = 0 :=
    λ d h4 h5, int_nonneg_dvd_prime_geom_sum_imp h h4 $ h5.trans $ dvd_of_eq h1.symm,
  replace h3 := h1 (y - 1) (le_of_lt h3) ⟨A, mul_comm A _⟩,
  rw [int.cast_sub, int.cast_one, sub_eq_zero, sub_eq_iff_eq_add, ← bit0] at h3,
  replace h2 := h1 A h2 ⟨y - 1, rfl⟩,
  replace h1 : (2 : zmod p) ≠ 0 := λ h4, nat.odd_iff_not_even.mp h0 $
    by rw [← nat.cast_two, zmod.nat_coe_zmod_eq_zero_iff_dvd,
      nat.prime_dvd_prime_iff_eq h nat.prime_two] at h4;
    exact cast (congr_arg _ h4.symm) even_two,
  set B : zmod p := ↑A with hB,
  conv_rhs at hB { rw int.cast_sum, congr, skip, funext, rw int.cast_pow },
  clear_value B; clear A,
  rw [← nat.prime_dvd_prime_iff_eq h nat.prime_three,
    ← zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.cast_succ],
  cases h3 with h3 h3,

  ---- Case 1: `y = 2`
  { replace hB := congr_arg (has_mul.mul (2 * (2 - 1))) hB,
    haveI : fact p.prime := ⟨h⟩,
    rw [h3, mul_assoc, mul_assoc, mul_geom_sum, bit0, add_sub_cancel, one_mul, mul_sub_one,
        ← pow_succ, bit0, ← nat.sub_sub, nat.sub_add_cancel (nat.sub_pos_of_lt h.one_lt),
        ← bit0, zmod.pow_card_sub_one_eq_one h1, bit0, sub_add_cancel', ← bit0] at hB,
    cases h2 with h2 h2,
    rwa [h2, mul_one, eq_neg_iff_add_eq_zero, ← nat.cast_two] at hB,
    rw [h2, mul_zero, zero_eq_neg] at hB,
    exact absurd hB one_ne_zero },

  ---- Case 2: `y = 1`
  { conv_rhs at hB { congr, skip, funext, rw [h3, one_pow] },
    rw [sum_const, card_range, nsmul_one, nat.cast_sub h.two_le, zmod.nat_cast_self] at hB,
    cases h2 with h2 h2,
    rwa [h2, eq_sub_iff_add_eq'] at hB,
    rw [hB, sub_eq_zero, nat.cast_two] at h2,
    exact absurd h2 h1.symm }
end





/-- Final solution -/
theorem final_solution {x y : ℤ} {p : ℕ} (h : p.prime) :
  good x y p ↔ (p = 2 ∧ x = -1) ∨ (p = 3 ∧ y = x ^ 2 + x + 2) :=
  ⟨λ h0, h.eq_two_or_odd'.imp
    (λ h1, ⟨h1, (p_eq_2_good_iff x y).mp $ cast (congr_arg _ h1) h0⟩)
    (λ h1, let h1 := p_eq_3_of_good_odd h h1 h0 in
      ⟨h1, (p_eq_3_good_iff x y).mp $ cast (congr_arg _ h1) h0⟩),
  λ h0, h0.elim
    (λ h1, cast (congr_arg _ h1.1.symm) $ (p_eq_2_good_iff x y).mpr h1.2)
    (λ h1, cast (congr_arg _ h1.1.symm) $ (p_eq_3_good_iff x y).mpr h1.2)⟩

end IMO2006N5
end IMOSL
