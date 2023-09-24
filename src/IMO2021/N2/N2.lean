import tactic.ring

/-! # IMO 2021 N2 (P1) -/

namespace IMOSL
namespace IMO2021N2

def good (n : ℕ) :=
  ∀ x : ℕ → bool, ∃ a b : ℕ, n ≤ a ∧ a < b ∧ b ≤ 2 * n ∧ x a = x b ∧ ∃ k, a + b = k ^ 2



lemma good_cond1 {n} (a b c k l m) (h : n ≤ a) (h0 : a < b) (h1 : b < c) (h2 : c ≤ 2 * n)
  (h3 : a + b = k ^ 2) (h4 : a + c = l ^ 2) (h5 : b + c = m ^ 2) : good n :=
  λ x, ((x a).eq_or_eq_bnot (x b)).elim (λ h6, ⟨a, b, h, h0, h1.le.trans h2, h6, k, h3⟩) $
    λ h6, ((x c).eq_or_eq_bnot (x b)).elim (λ h7, ⟨b, c, h.trans h0.le, h1, h2, h7.symm, m, h5⟩)
      (λ h7, ⟨a, c, h, h0.trans h1, h2, h6.trans h7.symm, l, h4⟩)

lemma good_cond2 {n} (h : ∃ k, n ≤ 2 * k ^ 2 + 4 * k ∧ k ^ 2 + 6 * k + 8 ≤ n) : good n :=
  exists.elim h $ λ k h, good_cond1 (2 * k ^ 2 + 4 * k) (2 * k ^ 2 + 8 * k + 9)
    (2 * (k ^ 2 + 6 * k + 8)) (2 * k + 3) (2 * k + 4) (2 * k + 5)
    h.1 (nat.lt_succ_of_le $ le_iff_exists_add.mpr ⟨4 * k + 8,
      (add_mul 4 4 k).symm ▸ (2 * k ^ 2).add_assoc (4 * k) (4 * k) ▸ add_assoc _ _ _⟩)
    (nat.lt_of_succ_le $ le_iff_exists_add.mpr
      ⟨4 * k + 6, (2 * k ^ 2 + 8 * k + 9).succ_eq_add_one.symm ▸ by ring⟩)
    (nat.mul_le_mul_left 2 h.2) (by ring) (by ring) (by ring)





/-- Final solution -/
theorem final_solution {n : ℕ} (h : 99 ≤ n) : good n :=
good_cond2 $ nat.le_induction
  ⟨7, nat.add_le_add_left (nat.succ_pos 27) 98, nat.le_refl 99⟩
  (λ n h h0, exists.elim h0 $ λ k h0, suffices 4 * k + 14 ≤ k ^ 2,
    from h0.1.lt_or_eq.elim (λ h1, ⟨k, h1, h0.2.trans n.le_succ⟩) $
      λ h1, h1.symm ▸ ⟨k + 1, le_iff_exists_add.mpr ⟨4 * k + 5, by ring⟩,
        by calc (k + 1) ^ 2 + 6 * (k + 1) + 8 = (4 * k + 14) + (k ^ 2 + 4 * k + 1) : by ring
        ... ≤ k ^ 2 + (k ^ 2 + 4 * k + 1) : nat.add_le_add_right this _
        ... = 2 * k ^ 2 + 4 * k + 1 : (add_assoc _ _ _).symm.trans $
          (two_mul $ k ^ 2).symm ▸ congr_arg nat.succ $ ((k ^ 2).add_assoc _ _).symm⟩,
  -- Now show that if `99 ≤ 2k^2 + 4k`, then `4k + 14 ≤ k^2`
  suffices 7 ≤ k, from (sq k).ge.trans' $
    (nat.add_le_add_left (nat.add_le_add this this) _).trans $
    ((4 * k).add_assoc k k).symm.trans_le $ nat.succ_mul 4 k ▸ nat.succ_mul 5 k ▸
      k.mul_le_mul_right ((nat.le_succ 6).trans this),
  nat.succ_le_of_lt $ lt_of_not_le $ λ h2, h.not_lt $ nat.lt_succ_of_le $ h0.1.trans $
    (nat.add_le_add (nat.mul_le_mul_left 2 $ nat.pow_le_pow_of_le_left h2 2)
      (nat.mul_le_mul_left 4 h2)).trans $ (nat.bit0_le $ nat.le_succ 48)) n h

end IMO2021N2
end IMOSL
