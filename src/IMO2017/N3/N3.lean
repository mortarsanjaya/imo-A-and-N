import
  data.nat.prime
  algebra.big_operators.intervals
  extra.periodic.big_operators
  ring_theory.int.basic

/-! # IMO 2017 N3 -/

namespace IMOSL
namespace IMO2017N3

open function finset extra



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

  -- The sequence is x_n = a - a = 0 if ab ∣ n and x_n = a - 0 = a otherwise
  refine ⟨λ i, a - dvd_seq (a * b) a i, λ i, by simp only [dvd_seq_add_self], _, λ i, _⟩,

  -- ab ∤ x_0 + x_1 + ... + x_{ab - 1} since the sum is a^2 b - a
  { rintros ⟨c, h1⟩,
    rw [sum_sub_distrib, sum_const, dvd_seq_sum, card_range, nsmul_eq_mul, nat.div_self hn,
        one_smul, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', ← mul_sub, nat.cast_mul, mul_assoc,
        mul_right_eq_self₀, nat.cast_eq_zero, or_iff_left (ne_of_gt (lt_trans one_pos h))] at h1,
    refine ne_of_gt h0 _,
    rw ← nat.dvd_one; use ((a : ℤ) - c).nat_abs,
    rw [← int.nat_abs_of_nat b, ← int.nat_abs_mul, h1, int.nat_abs_one] },
  cases lt_or_le (i % (a * b)) ((a - 1) * b) with h1 h1,

  -- If i % ab < (a - 1)b, pick j = b
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

  -- If i % ab ≥ (a - 1)b, pick j = b + 1
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



section cycle_sum

variables {n : ℕ} {s : ℕ → ℕ} (h : ∀ i : ℕ, i < s i)
include h

private lemma cycle_sum1 (k : ℕ) : strict_mono (λ i, s^[i] k) :=
begin
  intros i j h0; dsimp only [],
  rw [← nat.succ_le_iff, le_iff_exists_add] at h0,
  rcases h0 with ⟨c, rfl⟩,
  induction c with c c_ih,
  rw [add_zero, iterate_succ', comp_app]; exact h _,
  rw [nat.add_succ, iterate_succ', comp_app],
  exact lt_trans c_ih (h _)
end

variable (h0 : ∀ i : ℕ, s i < i + n)
include h0

private lemma cycle_sum2 (k i : ℕ) {c : ℕ} (h1 : 0 < c) : s^[i + c] k < (s^[i]) k + n * c :=
begin
  induction c with c c_ih,
  exfalso; exact lt_irrefl 0 h1,
  rcases c.eq_zero_or_pos with rfl | h2,
  rw [iterate_succ', comp_app, mul_one]; exact h0 _,
  rw [nat.add_succ, iterate_succ', comp_app, nat.mul_succ, ← add_assoc],
  refine lt_trans (h0 _) _,
  rw add_lt_add_iff_right; exact c_ih h2
end

private lemma cycle_sum3 (k : ℕ) : ∃ i j c : ℕ, 0 < c ∧ c < n ∧ (s^[j]) k = (s^[i]) k + n * c :=
begin
  have hn := lt_of_le_of_lt (nat.succ_le_iff.mpr (h 0)) (h0 0),
  rw [zero_add, ← nat.succ_le_iff] at hn,
  obtain ⟨i, j, h2, h3, h4⟩ : ∃ i j : ℕ, i < j ∧ j ≤ n ∧ (s^[i] k) % n = (s^[j] k) % n :=
  begin
    obtain ⟨i, h2, j, h3, h4, h5⟩ : ∃ (i : ℕ) (H : i ∈ range n.succ)
      (j : ℕ) (H : j ∈ range n.succ), i ≠ j ∧ (s^[i] k) % n = (s^[j] k) % n :=
    begin
      have h2 : (range n).card < (range n.succ).card :=
        by rw [card_range, card_range]; exact n.lt_succ_self,
      have h3 : ∀ i : ℕ, i ∈ range n.succ → (s^[i] k) % n ∈ range n :=
        λ i _, by rw mem_range; exact nat.mod_lt _ (lt_of_lt_of_le two_pos hn),
      exact exists_ne_map_eq_of_card_lt_of_maps_to h2 h3
    end,
    rw [mem_range, nat.lt_succ_iff] at h2 h3,
    rw ne_iff_lt_or_gt at h4,
    cases h4 with h4 h4,
    exacts [⟨i, j, h4, h3, h5⟩, ⟨j, i, h4, h2, eq_comm.mp h5⟩]
  end,
  have h5 := cycle_sum1 h k h2,
  rw [← nat.modeq, nat.modeq_iff_dvd' (le_of_lt h5)] at h4,
  cases h4 with c h4,
  rw [nat.sub_eq_iff_eq_add (le_of_lt h5), add_comm] at h4,
  refine ⟨i, j, c, _, _, h4⟩,
  { rw pos_iff_ne_zero; rintros rfl,
    rw [mul_zero, add_zero] at h4,
    exact ne_of_gt h5 h4 },
  { obtain ⟨d, rfl⟩ : ∃ d : ℕ, j = i + d := le_iff_exists_add.mp (le_of_lt h2),
    rw lt_add_iff_pos_right at h2,
    replace h5 := cycle_sum2 h h0 k i h2,
    dsimp only [] at h4 h5,
    rw [h4, add_lt_add_iff_left, mul_lt_mul_left (lt_of_lt_of_le two_pos hn)] at h5,
    exact lt_of_lt_of_le h5 (le_trans le_add_self h3) }
end

variables {x : ℕ → ℤ} (h1 : ∀ i : ℕ, (n : ℤ) ∣ (Ico i (s i)).sum x)
include h1

private lemma cycle_sum4 : ∃ m c : ℕ, 0 < c ∧ c < n ∧ (n : ℤ) ∣ (Ico m (m + n * c)).sum x :=
begin
  rcases cycle_sum3 h h0 0 with ⟨i, j, c, h2, h3, h4⟩,
  refine ⟨s^[i] 0, c, h2, h3, _⟩,
  dsimp only [] at h4; rw ← h4; clear h4 h3 h2 c,
  cases lt_or_le j i with h2 h2,
  rw [Ico_eq_empty_of_le (le_of_lt (cycle_sum1 h 0 h2)), sum_empty]; exact dvd_zero (n : ℤ),
  rw le_iff_exists_add at h2; rcases h2 with ⟨c, rfl⟩,
  induction c with c c_ih,
  rw [add_zero, Ico_self, sum_empty]; exact dvd_zero (n : ℤ),
  rw [nat.add_succ, iterate_succ', comp_app, ← finset.sum_Ico_consecutive x _ (le_of_lt (h _))],
  exacts [dvd_add c_ih (h1 _), (cycle_sum1 h 0).monotone le_self_add]
end

variable (h2 : periodic x n)
include h2

private lemma cycle_sum5 : ∃ c : ℕ, 0 < c ∧ c < n ∧ (n : ℤ) ∣ c * (range n).sum x :=
begin
  rcases cycle_sum4 h h0 h1 with ⟨m, c, h3, h4, h5⟩,
  refine ⟨c, h3, h4, _⟩,
  rw [finset.sum_Ico_eq_sum_range, nat.add_sub_cancel_left] at h5,
  convert h5; clear h3 h4 h5,
  induction c with c c_ih,
  rw [nat.cast_zero, zero_mul, mul_zero, sum_range_zero],
  rw [nat.cast_succ, add_one_mul, c_ih, nat.mul_succ, sum_range_add, add_right_inj],
  conv_rhs { congr, skip, funext, rw [← add_assoc, add_comm] },
  rw periodic_sum_const h2
end

end cycle_sum

/-- For `n ≥ 2`, if `n` is prime, then `n` is good. -/
private lemma prime_is_good {n : ℕ} (hn : 2 ≤ n) (h : n.prime) : good n :=
begin
  intros x hx h0; by_contra' h1,

  -- Using AOC, replace h0 with a special indexing sequence with a good property
  replace h1 := classical.axiom_of_choice h1,
  replace h1 : ∃ s : ℕ → ℕ, ∀ i : ℕ, i < s i ∧ s i < i + n ∧ (n : ℤ) ∣ (Ico i (s i)).sum x :=
  begin
    cases h1 with t h1,
    refine ⟨λ i, i + t i, λ i, ⟨_, _, (h1 i).2.2⟩⟩,
    rw lt_add_iff_pos_right; exact (h1 i).1,
    rw add_lt_add_iff_left; refine lt_of_le_of_ne (h1 i).2.1 (λ h2, _),
    replace h1 := (h1 i).2.2,
    rw [finset.sum_Ico_eq_sum_range, nat.add_sub_cancel_left] at h1,
    conv at h1 { find (_ + _) { rw add_comm } },
    rw [h2, periodic_sum_const hx] at h1,
    exact h0 h1
  end,

  -- Now just use the result given in the `cycle_sum` section to proceed
  replace h1 : ∃ c : ℕ, 0 < c ∧ c < n ∧ (n : ℤ) ∣ c * (range n).sum x :=
    by cases h1 with s h1; exact cycle_sum5 (λ i, (h1 i).1) (λ i, (h1 i).2.1) (λ i, (h1 i).2.2) hx,
  rcases h1 with ⟨c, h1, h2, h3⟩,
  replace h3 := int.prime.dvd_mul' h h3,
  rw [or_iff_left h0, int.coe_nat_dvd] at h3,
  exact nat.not_dvd_of_pos_of_lt h1 h2 h3
end



theorem final_solution {n : ℕ} (hn : 2 ≤ n) : good n ↔ n.prime :=
  ⟨good_is_prime hn, prime_is_good hn⟩

end IMO2017N3
end IMOSL
