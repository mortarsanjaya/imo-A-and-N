import number_theory.basic

/-! # IMO 2014 N4 -/

namespace IMOSL
namespace IMO2014N4

/- ### Extra lemmas -/

/-- If `k` is even `1 < m`, and `k ≡ 1 (mod m)`, then `k / m` is odd. -/
lemma even_modeq_one_div_odd {k m : ℕ} (h : even k) (h0 : 1 < m) (h1 : k ≡ 1 [MOD m]) :
  odd (k / m) :=
begin
  rw [nat.modeq, nat.mod_eq_of_lt h0] at h1,
  rw [← nat.div_add_mod k m, h1, nat.even_add_one, ← nat.odd_iff_not_even, nat.odd_mul] at h,
  exact h.2
end

/-- If `k` is even, then `2^k ≡ 1 (mod 3)`. -/
lemma two_pow_even_modeq_three_one {k : ℕ} (h : 2 ∣ k) : 2 ^ k ≡ 1 [MOD 3] :=
have 2 ^ 2 % 3 = 1,
  by rw [sq, two_mul, bit0, ← add_assoc, ← bit0, ← bit1, nat.add_mod_left, nat.one_mod],
exists.elim h $ λ a h, by rw [h, pow_mul, nat.modeq, nat.pow_mod, this, one_pow]





/- ### Start of the Problem -/

lemma case_big_odd {n : ℕ} (h : 1 < n) (h0 : odd n) (k : ℕ) :
  odd (n ^ (n ^ k) / n ^ k) :=
  cast (congr_arg _ (nat.pow_div (le_of_lt $ k.lt_pow_self h)
    (nat.one_pos.trans h)).symm) h0.pow

lemma case_big_odd_succ {n : ℕ} (h : 1 < n) (h0 : odd n) (k : ℕ) :
  odd ((n + 1) ^ (n ^ k.succ) / n ^ k.succ) :=
even_modeq_one_div_odd
((nat.even_pow' $ pow_ne_zero _ $ ne_of_gt $ pos_of_gt h).mpr $
  nat.even_add_one.mpr $ nat.odd_iff_not_even.mp h0)
(nat.one_lt_pow k.succ n k.succ_pos h)
(by have h2 := (pow_dvd_pow (n : ℤ) k.succ.le_succ).trans
  (dvd_sub_pow_of_dvd_sub (dvd_of_eq (add_sub_cancel (n : ℤ) 1).symm) k.succ);
rwa [one_pow, ← nat.cast_one, ← nat.cast_pow, ← nat.cast_add,
  ← nat.cast_pow, ← nat.modeq_iff_dvd, nat.modeq.comm] at h2)

lemma case_two (k : ℕ) :
  odd (2 ^ (2 ^ (2 * k.succ) * 3) / (2 ^ (2 * k.succ) * 3)) :=
begin
  have h : 0 < 2 := nat.succ_pos 1,
  have h0 : 1 < 3 := nat.succ_lt_succ h,
  have h1 : 2 * k.succ < 2 ^ (2 * k.succ) * 3 :=
    (nat.lt_two_pow _).trans (lt_mul_right (pow_pos h _) h0),
  rw [← nat.div_div_eq_div_mul, nat.pow_div (le_of_lt h1) h],
  exact even_modeq_one_div_odd
    (nat.even_pow.mpr ⟨even_two, ne_of_gt $ nat.sub_pos_of_lt h1⟩) h0
    (two_pow_even_modeq_three_one $ nat.dvd_sub'
      (dvd_mul_of_dvd_left (dvd_pow_self 2 $ ne_of_gt $ nat.mul_pos h k.succ_pos) 3)
      (dvd_mul_right 2 _))
end





/-- Final solution -/
theorem final_solution {n : ℕ} (h : 1 < n) : {k : ℕ | odd (n ^ k / k)}.infinite :=
(nat.even_or_odd n).symm.elim
  ---- Case 1: `n` is odd
  (λ h0, set.infinite_of_injective_forall_mem (nat.pow_right_injective h) (case_big_odd h h0)) $
λ h0, (eq_or_lt_of_le $ nat.succ_le_of_lt h).elim
  ---- Case 2: `n = 2`
  (λ h0, by rw ← h0; exact set.infinite_of_injective_forall_mem
    (λ a b h1, nat.succ_injective $ mul_right_injective₀ (nat.succ_ne_zero 1) $
      nat.pow_right_injective (le_refl 2) $ mul_left_injective₀ (nat.succ_ne_zero 2) h1)
    case_two)
  ---- Case 3: `n > 2` is even
  (λ h, begin
    cases n,
    exact absurd h (nat.not_lt_zero _),
    rw nat.succ_lt_succ_iff at h,
    exact set.infinite_of_injective_forall_mem
      ((nat.pow_right_injective $ nat.succ_le_of_lt h).comp nat.succ_injective)
      (case_big_odd_succ h $ nat.odd_iff_not_even.mpr $ nat.even_add_one.mp h0)
  end)

end IMO2014N4
end IMOSL
