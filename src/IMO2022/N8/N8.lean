import number_theory.legendre_symbol.jacobi_symbol

/-! # IMO 2022 N8 -/

namespace IMOSL
namespace IMO2022N8

lemma jacobi_sym_pow_odd'_eq_self (a : ℤ) (b n : ℕ) :
  jacobi_sym a b ^ (2 * n + 1) = jacobi_sym a b :=
(jacobi_sym.trichotomy a b).elim (λ h, h.symm ▸ zero_mul _) $
  λ h, h.elim (λ h, h.symm ▸ one_pow _) (λ h, h.symm ▸ (odd_two_mul_add_one n).neg_one_pow)

lemma two_pow_even'_mod_three (k : ℕ) : 2 ^ (2 * k) % 3 = 1 :=
  let h : 2 ^ 2 % 3 = 1 := rfl in (pow_mul 2 2 k).symm ▸
    (nat.pow_mod (2 ^ 2) k 3).symm ▸ h.symm ▸ congr_arg2 _ (one_pow k) rfl





/-- Final solution, general version: `N ≡ 5 [mod 60]` -/
theorem final_solution_general {N : ℕ} (h : N % 60 = 5)
  {n : ℕ} (h0 : 2 ^ n + N ∣ 5 ^ n - 3 ^ n) : n = 0 :=
let X : 3 ≤ 5 := nat.le_add_left 3 2, X0 : 5 % 3 = 2 := nat.add_mod_left 3 2 in
n.even_or_odd.elim
---- Case 1: `n` is even
(λ h1, (eq_or_ne n 0).resolve_right $ λ h2,
suffices 3 ∣ 5 ^ n, from nat.succ_ne_zero 1 $ X0.symm.trans $
  nat.mod_eq_zero_of_dvd $ nat.prime_three.dvd_of_dvd_pow this,
suffices 3 ∣ 2 ^ n + N, from nat.add_sub_of_le (nat.pow_le_pow_of_le_left X n) ▸
  (nat.dvd_add_right $ dvd_pow_self 3 h2).mpr (this.trans h0),
exists.elim h1 $ λ k h1, nat.dvd_iff_mod_eq_zero.mpr $ (nat.add_mod _ _ _).trans $
  h1.symm ▸ two_mul k ▸ (two_pow_even'_mod_three k).symm ▸
  nat.mod_mod_of_dvd N (⟨20, rfl⟩ : 3 ∣ 60) ▸ h.symm ▸ rfl)
---- Case 2: `n` is odd
(λ h1, begin
  rcases h1 with ⟨k, rfl⟩; cases k,
  -- Case 2.1: `n = 1`
  { rw [mul_zero, zero_add, pow_one, pow_one, pow_one] at h0,
    refine absurd (nat.le_of_dvd (nat.succ_pos 1) h0)
      (not_le_of_lt $ lt_add_of_pos_right _ $ nat.pos_of_ne_zero $ λ h1, absurd h _),
    rw [h1, nat.zero_mod],
    exact nat.zero_ne_bit1 2 },
  -- Case 2.2: `n = 2k + 3`
  { rw [← nat.modeq_iff_dvd' (nat.pow_le_pow_of_le_left X _), nat.modeq] at h0,
    replace h0 := congr_arg (coe : ℕ → ℤ) h0,
    rw [int.coe_nat_mod, int.coe_nat_mod, int.coe_nat_pow, int.coe_nat_pow] at h0,
    replace h0 := jacobi_sym.mod_left' h0,
    rw [jacobi_sym.pow_left, jacobi_sym_pow_odd'_eq_self,
        jacobi_sym.pow_left, jacobi_sym_pow_odd'_eq_self] at h0,
    have h1 : (2 ^ (2 * k.succ + 1) + N) % 4 = 1 :=
      by rw [nat.add_mod, ← nat.mod_mod_of_dvd N (⟨15, rfl⟩ : 4 ∣ 60), h, ← nat.add_mod,
        pow_succ, nat.mul_succ, pow_add, ← mul_assoc, sq, two_mul 2, ← bit0, nat.mul_add_mod];
      exact nat.add_mod_left 4 1,
    refine absurd ((jacobi_sym.quadratic_reciprocity_one_mod_four h1 ⟨1, rfl⟩).trans
      $ h0.trans $ jacobi_sym.quadratic_reciprocity_one_mod_four' ⟨2, rfl⟩ h1) _,
    clear h0 h1,
    suffices : jacobi_sym ↑(2 ^ (2 * k.succ + 1) + N) 3 = 1 ∧
      jacobi_sym ↑(2 ^ (2 * k.succ + 1) + N) 5 = -1,
      rw [mul_one, this.1, this.2, eq_neg_self_iff]; exact one_ne_zero' ℤ,
    split,

    -- `J(2^(2k + 1) + N | 3) = 1`
    { rw [jacobi_sym.mod_left _ 3, ← int.coe_nat_mod, nat.add_mod,
        ← nat.mod_mod_of_dvd N (⟨20, rfl⟩ : 3 ∣ 60), h, X0, pow_succ,
        nat.mul_mod, two_pow_even'_mod_three, mul_one, nat.mod_mod],
      exact jacobi_sym.one_left 3 },

    -- `J(2^(2k + 1) + N | 5) = -1`
    { rw [jacobi_sym.mod_left _ 5, ← int.coe_nat_mod, nat.add_mod,
        ← nat.mod_mod_of_dvd N (⟨12, rfl⟩ : 5 ∣ 60), h, nat.mod_self, add_zero,
        nat.mod_mod, int.coe_nat_mod, ← jacobi_sym.mod_left, int.coe_nat_pow,
        jacobi_sym.pow_left, jacobi_sym_pow_odd'_eq_self, nat.cast_two],
      exact (jacobi_sym.at_two ⟨2, rfl⟩).trans rfl } }
end)

/-- Final solution, original version -/
theorem final_solution {n : ℕ} (h : 2 ^ n + 65 ∣ 5 ^ n - 3 ^ n) : n = 0 :=
  final_solution_general (nat.add_mod_left 60 5) h

end IMO2022N8
end IMOSL
