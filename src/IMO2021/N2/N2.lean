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
  exists.elim h $ λ k h,  good_cond1 (2 * k ^ 2 + 4 * k) (2 * k ^ 2 + 8 * k + 9)
    (2 * (k ^ 2 + 6 * k + 8)) (2 * k + 3) (2 * k + 4) (2 * k + 5)
    h.1 (nat.lt_succ_of_le $ le_iff_exists_add.mpr ⟨4 * k + 8, by ring⟩)
    (nat.lt_of_succ_le $ le_iff_exists_add.mpr
      ⟨4 * k + 6, (2 * k ^ 2 + 8 * k + 9).succ_eq_add_one.symm ▸ by ring⟩)
    (nat.mul_le_mul_left 2 h.2) (by ring) (by ring) (by ring)





/-- Final solution -/
theorem final_solution {n : ℕ} (h : 99 ≤ n) : good n :=
good_cond2 $ nat.le_induction
  ⟨7, nat.add_le_add_left (nat.succ_pos 27) 98, nat.le_refl 99⟩
  (λ n h h0, begin
    rcases h0 with ⟨k, h0, h1⟩,
    rw le_iff_lt_or_eq at h0,
    rcases h0 with h0 | rfl,
    ---- Case 1: `n < 2k^2 + 4k`
    exact ⟨k, h0, h1.trans n.le_succ⟩,
    ---- Case 2: `n = 2k^2 + 4k`
    refine ⟨k + 1, le_iff_exists_add.mpr ⟨4 * k + 5, by ring⟩, _⟩,
    calc (k + 1) ^ 2 + 6 * (k + 1) + 8 = (4 * k + 14) + (k ^ 2 + 4 * k + 1) : by ring
    ... ≤ k ^ 2 + (k ^ 2 + 4 * k + 1) : nat.add_le_add_right _ _
    ... = 2 * k ^ 2 + 4 * k + 1 : by ring,

    ---- It remains to show that if `99 ≤ 2k^2 + 4k`, then `4k + 14 ≤ k^2`
    suffices : 7 ≤ k,
    { rw [bit0_eq_two_mul 7, sq],
      calc 4 * k + 2 * 7 ≤ 4 * k + 2 * k :
        nat.add_le_add_left (nat.mul_le_mul_left 2 this) _
      ... = 6 * k : (add_mul 4 2 k).symm
      ... ≤ k * k : k.mul_le_mul_right ((nat.le_succ 6).trans this) },
  
    refine nat.succ_le_of_lt (lt_of_not_le $ λ h2, h.not_lt _),
      calc _ ≤ 2 * 6 ^ 2 + 4 * 6 : nat.add_le_add
      (nat.mul_le_mul_left _ $ nat.pow_le_pow_of_le_left h2 2) (nat.mul_le_mul_left 4 h2)
    ... < 99 : by norm_num
  end) n h

end IMO2021N2
end IMOSL
