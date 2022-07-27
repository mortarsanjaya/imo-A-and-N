import data.nat.prime data.nat.choose.basic

/-! # IMO 2012 N3 -/

namespace IMOSL
namespace IMO2012N3

def good (m : ℕ) := 2 ≤ m ∧ ∀ n : ℕ, 2 * n ≤ m → m ≤ 3 * n → n ∣ n.choose (m - 2 * n)



private lemma prime_implies_good (p : ℕ) (h : p.prime) : good p :=
begin
  split,
  exact nat.prime.two_le h,
  rintros n h0 h1,
  have hn : 0 < n := pos_of_mul_pos_right (lt_of_lt_of_le h.pos h1) zero_le_three,
  rcases h.eq_two_or_odd with rfl | h2,
  { rw ← nat.succ_le_iff at hn,
    replace hn := nat.mul_le_mul_left 2 hn,
    rw mul_one at hn,
    replace hn := le_antisymm h0 hn,
    rw nat.mul_right_eq_self_iff two_pos at hn,
    rw hn; exact one_dvd _ },
  apply @nat.coprime.dvd_of_dvd_mul_right _ (p - 2 * n),
  { rw [nat.coprime, nat.gcd_rec, ← nat.add_mul_mod_self_right _ 2,
        nat.sub_add_cancel h0, ← nat.gcd_rec, nat.gcd_comm],
    exact nat.coprime_of_lt_prime hn (lt_of_lt_of_le (lt_two_mul_self hn) h0) h },
  { obtain ⟨k, h3⟩ : ∃ k : ℕ, p - 2 * n = k + 1 :=
    begin
      use (p - 2 * n).pred,
      rw [← nat.succ_eq_add_one, nat.succ_pred_eq_of_pos],
      apply nat.pos_of_ne_zero; intros h3,
      replace h3 := le_antisymm (nat.sub_eq_zero_iff_le.mp h3) h0,
      rw [h3, nat.mul_mod_right] at h2,
      exfalso; exact zero_ne_one h2
    end,
    rw [h3, nat.choose_succ_right_eq],
    cases n,
    exfalso; exact lt_irrefl 0 hn,
    rw [nat.succ_eq_add_one, ← nat.choose_mul_succ_eq],
    use (n.choose k); rw mul_comm }
end




end IMO2012N3
end IMOSL
