import data.nat.choose.basic data.nat.parity

/-! # IMO 2012 N3 -/

namespace IMOSL
namespace IMO2012N3

def good (m : ℕ) := 1 < m ∧ ∀ n : ℕ, 2 * n ≤ m → m ≤ 3 * n → n ∣ n.choose (m - 2 * n)



private theorem prime_implies_good (p : ℕ) (h : p.prime) : good p :=
begin
  refine ⟨nat.prime.one_lt h, λ n h0 h1, _⟩,
  replace h1 : 0 < n := pos_of_mul_pos_right (lt_of_lt_of_le h.pos h1) zero_le_three,
  rcases h.eq_two_or_odd with rfl | h2,
  { replace h1 := nat.mul_le_mul_left 2 h1,
    rw mul_one at h1,
    replace h1 := le_antisymm h0 h1,
    rw nat.mul_right_eq_self_iff two_pos at h1,
    rw h1; exact one_dvd _ },
  apply @nat.coprime.dvd_of_dvd_mul_right _ (p - 2 * n),
  { rw [nat.coprime, nat.gcd_rec, ← nat.add_mul_mod_self_right _ 2,
        nat.sub_add_cancel h0, ← nat.gcd_rec, nat.gcd_comm],
    exact nat.coprime_of_lt_prime h1 (lt_of_lt_of_le (lt_two_mul_self h1) h0) h },
  { rw le_iff_exists_add at h0,
    rcases h0 with ⟨k, rfl⟩,
    rcases k with rfl | k,
    rw [add_zero, nat.mul_mod_right] at h2,
    exfalso; exact zero_ne_one h2,
    rw [nat.add_sub_cancel_left, nat.choose_succ_right_eq],
    cases n,
    exfalso; exact lt_irrefl 0 h1,
    rw [nat.succ_eq_add_one, ← nat.choose_mul_succ_eq],
    exact dvd_mul_left (n + 1) (nat.choose n k) }
end

private lemma lem1 {m : ℕ} (h : 1 < m) : 2 ∣ m ∨ ∃ p k : ℕ, p.prime ∧ m = p * (2 * k + 1) :=
begin
  let p := m.min_fac,
  cases eq_or_ne p 2 with h0 h0,
  left; rwa ← nat.min_fac_eq_two_iff,
  rw [ne.def, nat.min_fac_eq_two_iff, nat.two_dvd_ne_zero, ← nat.odd_iff] at h0,
  obtain ⟨c, h1⟩ : p ∣ m := nat.min_fac_dvd m,
  rw h1 at h0; replace h0 := nat.odd.of_mul_right h0,
  rcases h0 with ⟨k, rfl⟩,
  right; exact ⟨p, k, nat.min_fac_prime (ne_of_gt h), h1⟩
end

private lemma lem2 {p : ℕ} (h : p.prime) (k r : ℕ) (h0 : r < p) :
  ¬p ∣ (p * k + r).desc_factorial r :=
begin
  induction r with r r_ih; intros h1,
  rw [nat.desc_factorial_zero, nat.dvd_one] at h1,
  rw h1 at h; exact nat.not_prime_one h,
  rw [nat.succ_eq_add_one r, ← add_assoc, nat.succ_desc_factorial_succ, add_assoc,
      ← nat.succ_eq_add_one, nat.prime.dvd_mul h, ← nat.dvd_add_iff_right ⟨k, rfl⟩,
      or_iff_left (r_ih (lt_trans (lt_add_one r) h0))] at h1,
  exact nat.not_dvd_of_pos_of_lt r.succ_pos h0 h1
end

private theorem good_implies_prime (m : ℕ) (h : good m) : nat.prime m :=
begin
  cases h with h0 h,
  replace h0 := lem1 h0,
  rcases h0 with ⟨k, rfl⟩ | ⟨p, k, hp, rfl⟩,
  { replace h := h k (le_refl _) (nat.mul_le_mul_right k (by norm_num)),
    rw [nat.sub_self, nat.choose_zero_right, nat.dvd_one] at h,
    rw [h, mul_one]; exact nat.prime_two },
  { rcases k.eq_zero_or_pos with rfl | h0,
    rwa [mul_zero, zero_add, mul_one],
    replace h := h (p * k),
    rw [mul_add_one, bit1, add_one_mul 2, mul_left_comm, nat.add_sub_cancel_left] at h,
    replace h := h le_self_add (by rw [add_le_add_iff_left]; exact nat.le_mul_of_pos_right h0),
    exfalso; rw [← nat.succ_le_iff, le_iff_exists_add] at h0,
    rcases h0 with ⟨k, rfl⟩,
    apply lem2 hp k (p - 1) (nat.sub_lt hp.pos one_pos),
    rw [← nat.mul_dvd_mul_iff_left (mul_pos hp.pos k.succ_pos), nat.mul_succ],
    nth_rewrite 4 ← nat.sub_add_cancel hp.pos,
    rw [← add_assoc, ← nat.succ_desc_factorial_succ, add_assoc, nat.sub_add_cancel hp.pos,
        nat.desc_factorial_eq_factorial_mul_choose, ← mul_add_one, add_comm, mul_comm],
    exact mul_dvd_mul (nat.dvd_factorial hp.pos (le_refl p)) h }
end



/-- Final solution -/
theorem final_solution : good = nat.prime :=
  by ext n; exact ⟨good_implies_prime n, prime_implies_good n⟩

end IMO2012N3
end IMOSL
