import data.nat.choose.basic data.nat.parity

/-! # IMO 2012 N3 -/

namespace IMOSL
namespace IMO2012N3

private lemma prime_not_dvd_desc_factorial {p : ℕ} (h : p.prime) (k : ℕ) {r : ℕ} (h0 : r < p) :
   ¬p ∣ (p * k + r).desc_factorial r :=
 begin
  induction r with r h1,
  rw nat.desc_factorial_zero; exact h.not_dvd_one,
  rw [nat.add_succ, nat.succ_desc_factorial_succ, add_assoc, h.dvd_mul,
      nat.dvd_add_right ⟨k, rfl⟩, or_iff_right (nat.not_dvd_of_pos_of_lt r.succ_pos h0)],
  exact h1 (lt_trans r.lt_succ_self h0)
 end



/-- Final solution -/
theorem final_solution {m : ℕ} (h : 1 < m) :
  (∀ n : ℕ, 2 * n ≤ m → n ∣ n.choose (m - 2 * n)) ↔ m.prime :=
begin
  symmetry; refine ⟨λ h0 n h1, _, λ h0, _⟩,

  ---- If `m` is prime, then `n ∣ C(n, m - 2n)` for any `n ≤ m/2`
  { -- Case 1: `n = 0`
    clear h; rcases n.eq_zero_or_pos with rfl | h,
    rw [mul_zero, nat.sub_zero, zero_dvd_iff, nat.choose_eq_zero_iff],
    exact h0.pos,

    -- Case 2: `m = 2`, `n = 1`
    rcases h0.eq_two_or_odd with rfl | h2,
    replace h1 : n = 1 := le_antisymm ((mul_le_iff_le_one_right two_pos).mp h1) h,
    rw [h1, mul_one, nat.sub_self, nat.choose_succ_self_right],
  
    -- Case 3: `m` is an odd prime
    rw le_iff_exists_add at h1,
    rcases h1 with ⟨k, rfl⟩,
    rw [add_comm, nat.add_mul_mod_self_left] at h2,
    replace h2 : ∃ q : ℕ, q + 1 = k :=
      ⟨2 * (k / 2), by nth_rewrite 2 ← h2; exact nat.div_add_mod k 2⟩,
    rcases h2 with ⟨q, rfl⟩,
    replace h0 := nat.coprime_of_lt_prime q.succ_pos
      ((lt_add_iff_pos_left _).mpr (mul_pos two_pos h)) h0,
    rw nat.coprime_add_self_left at h0; replace h0 := h0.coprime_mul_left,
    rw [← nat.succ_le_iff, le_iff_exists_add'] at h,
    rcases h with ⟨n, rfl⟩,
    rw [nat.add_sub_cancel_left, ← h0.dvd_mul_right,
        nat.choose_succ_right_eq, ← nat.choose_mul_succ_eq],
    exact dvd_mul_left (n + 1) (n.choose q) },

  ---- If `n ∣ C(n, m - 2n)` for any `n ≤ m/2`, then `m` is prime
  { -- First, solve the case where `m` is even
    by_cases h1 : 2 ∣ m,
    rcases h1 with ⟨r, rfl⟩,
    replace h0 := h0 r (le_refl _),
    rw [nat.sub_self, nat.choose_zero_right, nat.dvd_one] at h0,
    rw [h0, mul_one]; exact nat.prime_two,

    -- Some setup for the case where `m` is odd
    rcases nat.min_fac_dvd m with ⟨r, h2⟩,
    rw h2 at h1; replace h1 : ¬2 ∣ r := λ h3,
      by exfalso; exact h1 (dvd_mul_of_dvd_right h3 (nat.min_fac m)),
    rw [nat.prime_def_min_fac, nat.succ_le_iff, and_iff_right h],
    replace h := nat.min_fac_prime (ne_of_gt h),
    generalize_hyp : m.min_fac = p at h h2 ⊢,
    subst h2; rw [eq_comm, mul_right_eq_self₀, or_iff_left h.ne_zero],
    replace h1 : ∃ k : ℕ, 2 * k + 1 = r :=
      ⟨r / 2, by nth_rewrite 2 ← nat.two_dvd_ne_zero.mp h1; exact nat.div_add_mod r 2⟩,
    rcases h1 with ⟨k, rfl⟩,
    rw [add_left_eq_self, nat.mul_eq_zero, or_iff_right (two_ne_zero : 2 ≠ 0)],
    
    -- Now choose `n = pk` and do the work
    replace h0 := h0 (p * k),
    rw [mul_left_comm, mul_add_one, nat.add_sub_cancel_left] at h0,
    replace h0 := dvd_mul_of_dvd_right (h0 le_self_add) (p - 1).factorial,
    contrapose! h0; rw [← zero_lt_iff, ← nat.succ_le_iff, le_iff_exists_add'] at h0,
    rcases h0 with ⟨k, rfl⟩,
    rw [← nat.mul_dvd_mul_iff_left (p - 1).succ_pos, nat.mul_succ, ← mul_assoc,
        ← nat.factorial_succ, nat.succ_eq_add_one, nat.sub_add_cancel h.pos,
        ← nat.desc_factorial_eq_factorial_mul_choose],
    have h0 := prime_not_dvd_desc_factorial h k (nat.sub_lt h.pos one_pos),
    rwa [← nat.mul_dvd_mul_iff_left (p * k + (p - 1)).succ_pos, ← nat.succ_desc_factorial_succ,
         nat.succ_eq_add_one, add_assoc, nat.sub_add_cancel h.pos, mul_comm] at h0 }
end

end IMO2012N3
end IMOSL
