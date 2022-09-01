import data.nat.prime algebra.big_operators.intervals algebra.periodic

/-! # IMO 2017 N3 -/

namespace IMOSL
namespace IMO2017N3

open function finset

def good (n : ℕ) := ∀ x : ℕ → ℤ, periodic x n → ¬(n : ℤ) ∣ (range n).sum x →
  ∃ i : ℕ, ∀ j : ℕ, 0 < j → j ≤ n → ¬(n : ℤ) ∣ (Ico i (i + j)).sum x



section dvd_indicator

variables {M : Type*} [add_comm_monoid M]

private def dvd_seq (n : ℕ) (c : M) (i : ℕ) := ite (n ∣ i.succ) c 0

private lemma dvd_seq_dvd (n : ℕ) (c : M) {i : ℕ} (h : n ∣ i.succ) : dvd_seq n c i = c :=
  by rw [dvd_seq, if_pos h]

private lemma dvd_seq_not_dvd (n : ℕ) (c : M) {i : ℕ} (h : ¬n ∣ i.succ) : dvd_seq n c i = 0 :=
  by rw [dvd_seq, if_neg h]

private lemma dvd_seq_add_self (n : ℕ) (c : M) (i : ℕ) : dvd_seq n c (i + n) = dvd_seq n c i :=
begin
  unfold dvd_seq; congr' 1,
  rw [nat.succ_eq_add_one, add_right_comm, nat.dvd_add_self_right]
end

private lemma dvd_seq_mod_self (n : ℕ) (c : M) (i : ℕ) : dvd_seq n c (i % n) = dvd_seq n c i :=
begin
  unfold dvd_seq; congr' 1,
  rw [nat.succ_eq_add_one, nat.dvd_iff_mod_eq_zero, nat.mod_add_mod, nat.dvd_iff_mod_eq_zero]
end

private lemma dvd_seq_sum (n : ℕ) (c : M) (k : ℕ) :
  (range k).sum (dvd_seq n c) = (k / n) • c :=
begin
  induction k with k k_ih,
  rw [sum_range_zero, nat.zero_div, zero_smul],
  rw [sum_range_succ, k_ih, dvd_seq, nat.succ_div, add_smul, ite_smul, one_smul, zero_smul]
end

end dvd_indicator



/-- For `n ≥ 2`, if `n` is good, then `n` is prime. -/
private lemma good_is_prime {n : ℕ} (hn : 2 ≤ n) (h : good n) : n.prime :=
begin
  rw [nat.prime_def_lt'', and_iff_right hn],
  unfold good at h; contrapose! h,
  rcases h with ⟨a, ⟨b, rfl⟩, h, h0⟩,
  rw [ne.def, eq_comm, mul_right_eq_self₀, not_or_distrib, ← ne.def] at h0,
  rw [ne_iff_lt_or_gt, nat.lt_succ_iff, gt_iff_lt, nonpos_iff_eq_zero] at h h0,
  rw or_iff_right h0.2 at h; rcases h0 with ⟨h0, -⟩,
  rcases h0 with rfl | h0,
  rw mul_zero at hn,
  exfalso; exact not_lt_of_le hn two_pos,
  replace hn := lt_of_lt_of_le two_pos hn,
  refine ⟨λ i, a - dvd_seq (a * b) a i, λ i, by simp only [dvd_seq_add_self], _, λ i, _⟩,
  { rintros ⟨c, h1⟩,
    rw [sum_sub_distrib, sum_const, dvd_seq_sum, card_range, nsmul_eq_mul, nat.div_self hn,
        one_smul, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', ← mul_sub, nat.cast_mul, mul_assoc,
        mul_right_eq_self₀, nat.cast_eq_zero, or_iff_left (ne_of_gt (lt_trans one_pos h))] at h1,
    refine ne_of_gt h0 _,
    rw ← nat.dvd_one; use ((a : ℤ) - c).nat_abs,
    rw [← int.nat_abs_of_nat b, ← int.nat_abs_mul, h1, int.nat_abs_one] },
  cases lt_or_le (i % (a * b)) ((a - 1) * b) with h1 h1,
  { refine ⟨b, lt_trans one_pos h0, nat.le_mul_of_pos_left (lt_trans one_pos h), 1, _⟩,
    rw [mul_one, sum_sub_distrib, sum_const, nat.card_Ico, nsmul_eq_mul,
        nat.add_sub_cancel_left, mul_comm, nat.cast_mul, sub_eq_self,
        finset.sum_Ico_eq_add_neg _ le_self_add, dvd_seq_sum, add_neg_eq_zero, dvd_seq_sum],
    generalize hr : i % (a * b) = r,
    rw hr at h1,
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, r + q * (a * b) = i :=
      ⟨i / (a * b), by rw ← hr; exact nat.mod_add_div' i (a * b)⟩,
    suffices : r + b < a * b,
    { rw [add_right_comm, nat.add_mul_div_right _ _ hn, nat.div_eq_of_lt this,
          nat.add_mul_div_right _ _ hn, nat.div_eq_of_lt (lt_trans _ this)],
      rw lt_add_iff_pos_right; exact lt_trans one_pos h0 },
    convert nat.add_lt_add_right h1 b,
    rw [← add_one_mul, nat.sub_add_cancel (le_of_lt h)] },
  { have h2 : b.succ < a * b :=
    begin
      cases a with a a,
      exfalso; exact lt_asymm h one_pos,
      rw [nat.succ_mul, nat.succ_eq_one_add, add_lt_add_iff_right],
      exact lt_of_lt_of_le h0 (le_mul_of_one_le_left' (nat.lt_succ_iff.mp h))
    end,
    refine ⟨b.succ, b.succ_pos, le_of_lt h2, 1, _⟩,
    rw [mul_one, sum_sub_distrib, sum_const, nat.card_Ico, nat.add_sub_cancel_left,
        succ_nsmul', nsmul_eq_mul, mul_comm, nat.cast_mul, sub_eq_iff_eq_add,
        add_right_inj, finset.sum_Ico_eq_add_neg _ le_self_add, dvd_seq_sum,
        dvd_seq_sum, nat.add_div_eq_of_le_mod_add_mod _ hn, nat.div_eq_of_lt h2,
        add_zero, succ_nsmul, add_neg_cancel_right],
    rw nat.mod_eq_of_lt h2,
    convert add_le_add h1 (le_of_lt b.lt_succ_self),
    rw [← add_one_mul, nat.sub_add_cancel (le_of_lt h)] }
end

/-- For `n ≥ 2`, if `n` is prime, then `n` is good. -/
private lemma prime_is_good {n : ℕ} (hn : 2 ≤ n) (h : n.prime) : good n :=
begin
  sorry
end



/-- Final solution -/
theorem final_solution {n : ℕ} (hn : 2 ≤ n) : good n ↔ n.prime :=
  ⟨good_is_prime hn, prime_is_good hn⟩

end IMO2017N3
end IMOSL
