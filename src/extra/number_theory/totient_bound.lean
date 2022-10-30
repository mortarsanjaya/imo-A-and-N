import data.nat.totient

/-!
# Bounds on the totient function

This file proves some bound on the totient function.
The main interest is to solve 2020 N4 by characterizing all `n : ℕ` such that `φ(n) ≤ 2`.
-/

namespace IMOSL
namespace extra

lemma totient_big_prime_div {p : ℕ} (hp : p.prime) (h : 3 < p) {n : ℕ} (h0 : 0 < n) (h1 : p ∣ n) :
  2 < n.totient :=
begin
  refine lt_of_lt_of_le _ (nat.le_of_dvd (nat.totient_pos h0) (nat.totient_dvd_of_dvd h1)),
  rwa [nat.totient_prime hp, lt_tsub_iff_right, ← bit1]
end

lemma totient_le_two_eq_two_pow_times_three_pow {n : ℕ} (h : 0 < n) (h0 : n.totient ≤ 2) :
  ∃ a b : ℕ, n = 2 ^ a * 3 ^ b :=
begin
  refine ⟨n.factorization 2, n.factorization 3, _⟩,
  suffices : n.factorization.support ⊆ {2, 3},
  { nth_rewrite 0 ← nat.factorization_prod_pow_eq_self (ne_of_gt h),
    rw [finsupp.prod_of_support_subset _ this, finset.prod_insert, finset.prod_singleton],
    rw finset.mem_singleton; exact nat.bit0_ne_bit1 _ _,
    rintros p -; exact pow_zero p },
  intros p h1; contrapose! h0,
  have h2 : p.prime := nat.prime_of_mem_factorization h1,
  replace h1 := nat.dvd_of_mem_factorization h1,
  refine totient_big_prime_div h2 _ h h1,
  contrapose! h0; rw [finset.mem_insert, finset.mem_singleton],
  rw [le_iff_lt_or_eq, nat.lt_succ_iff, le_iff_lt_or_eq, nat.lt_succ_iff, or_assoc] at h0,
  cases h0 with h0 h0,
  rw [le_iff_lt_or_eq, nat.lt_one_iff] at h0,
  exfalso; rcases h0 with rfl | rfl,
  exacts [nat.not_prime_zero h2, nat.not_prime_one h2, h0]
end

lemma big_two_lt_totient {n : ℕ} (h : 6 < n) : 2 < n.totient :=
begin
  rw ← not_le; intros h0,
  obtain ⟨a, b, rfl⟩ := totient_le_two_eq_two_pow_times_three_pow (pos_of_gt h) h0,
  revert h; rw [imp_false, not_lt],
  replace h0 := le_trans (nat.totient_super_multiplicative _ _) h0,
  have h := nat.totient_prime_pow_succ nat.prime_two,
  rw [bit0, nat.add_sub_cancel, ← bit0] at h; simp only [mul_one] at h,
  cases b with _ b,
  { rw [pow_zero, nat.totient_one, mul_one] at h0,
    rw [pow_zero, mul_one],
    cases a with _ a,
    rw pow_zero; norm_num,
    rw h at h0; rw pow_succ,
    refine le_trans (nat.mul_le_mul_left 2 h0) _,
    norm_num },
  { rw [nat.totient_prime_pow_succ nat.prime_three, bit1, nat.add_sub_cancel, ← bit1,
        ← mul_assoc, mul_le_iff_le_one_left (two_pos : 0 < 2), le_iff_eq_or_lt,
        nat.mul_eq_one_iff, nat.lt_one_iff, mul_eq_zero, nat.totient_eq_one_iff] at h0,
    clear h; rcases h0 with ⟨h | h, h0⟩ | h | h,
    rw [h, one_mul, pow_succ, h0, mul_one]; norm_num,
    rw [h, pow_succ, h0, mul_one]; norm_num,
    exfalso; exact ne_of_gt (nat.totient_pos (pow_pos two_pos a)) h,
    exfalso; refine ne_of_gt (pow_pos _ b) h; exact three_pos }
end



end extra
end IMOSL
