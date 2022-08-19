import data.nat.choose.basic data.nat.parity

/-! # IMO 2012 N3 -/

namespace IMOSL
namespace IMO2012N3

def good (m : ℕ) := 2 ≤ m ∧ ∀ n : ℕ, 2 * n ≤ m → m ≤ 3 * n → n ∣ n.choose (m - 2 * n)



private lemma prime_implies_good (p : ℕ) (h : p.prime) : good p :=
begin
  refine ⟨nat.prime.two_le h, λ n h0 h1, _⟩,
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

private lemma good_implies_prime (m : ℕ) (h : good m) : nat.prime m :=
begin
  cases h with h h0,
  let p := m.min_fac,
  cases eq_or_ne p 2 with h1 h1,
  { rw nat.min_fac_eq_two_iff at h1,
    rcases h1 with ⟨k, rfl⟩,
    replace h0 := h0 k (le_refl _) (nat.mul_le_mul_right k (by norm_num)),
    rw [nat.sub_self, nat.choose_zero_right, nat.dvd_one] at h0,
    rw [h0, mul_one]; exact nat.prime_two },
  { obtain ⟨k, h2⟩ : p ∣ m := nat.min_fac_dvd m,
    have h3 : nat.prime p := nat.min_fac_prime (by rintros rfl; exact not_lt_of_le h one_lt_two),
    rw [ne.def, nat.min_fac_eq_two_iff, h2, nat.two_dvd_ne_zero, ← nat.odd_iff] at h1,
    replace h1 := nat.odd.of_mul_right h1,
    rcases h1 with ⟨k, rfl⟩,
    rcases k.eq_zero_or_pos with rfl | h1,
    rw [h2, mul_zero, zero_add, mul_one]; exact h3,
    exfalso,
    replace h0 : (p * k) ∣ (p * k).choose (m - 2 * (p * k)) :=
    begin
      apply h0,
      rw [h2, mul_add_one, mul_left_comm]; exact le_self_add,
      rw [h2, mul_add_one, mul_left_comm, bit1, add_one_mul 2],
      exact nat.add_le_add_left (nat.le_mul_of_pos_right h1) _
    end,
    rw [h2, mul_left_comm, mul_add_one, nat.add_sub_cancel_left] at h0,
    replace h0 := mul_dvd_mul (nat.dvd_factorial h3.pos (le_refl p)) h0,
    rw ← nat.desc_factorial_eq_factorial_mul_choose at h0,
    nth_rewrite 1 ← nat.sub_add_cancel h1 at h0,
    rw mul_add_one at h0,
    nth_rewrite 3 ← nat.sub_add_cancel h3.pos at h0,
    nth_rewrite 4 ← nat.sub_add_cancel h3.pos at h0,
    rw [← add_assoc, nat.succ_desc_factorial_succ, add_assoc,
        nat.sub_add_cancel h3.pos, ← mul_add_one, nat.sub_add_cancel h1,
        mul_comm, nat.mul_dvd_mul_iff_left (mul_pos h3.pos h1)] at h0,
    clear_value p; clear h h2 m; revert h0,
    generalize_hyp h : p - 1 = r,
    replace h : r ≤ p - 1 := ge_of_eq h,
    induction r with r r_ih; intros h0,
    rw [nat.desc_factorial_zero, nat.dvd_one] at h0,
    rw h0 at h3; exact nat.not_prime_one h3,
    rw [nat.succ_eq_add_one r, ← add_assoc, nat.succ_desc_factorial_succ, add_assoc,
        ← nat.succ_eq_add_one, nat.prime.dvd_mul h3, ← nat.dvd_add_iff_right ⟨k - 1, rfl⟩] at h0,
    cases h0 with h0 h0,
    rw [← nat.add_le_add_iff_right, nat.sub_add_cancel h3.pos, ← nat.lt_iff_add_one_le] at h,
    exact ne_of_gt (nat.succ_pos r) (nat.eq_zero_of_dvd_of_lt h0 h),
    exact r_ih (le_trans (nat.le_succ r) h) h0 }
end



/-- Final solution -/
theorem final_solution : good = nat.prime :=
  by ext n; exact ⟨good_implies_prime n, prime_implies_good n⟩

end IMO2012N3
end IMOSL
