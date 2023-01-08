import algebra.big_operators.intervals number_theory.divisors

/-! # IMO 2006 N3 -/

namespace IMOSL
namespace IMO2006N3

open finset

section extra_lemmas

private lemma exists_sup_fn_fin (f : ℕ → ℕ) : ∀ c : ℕ, ∃ K : ℕ, ∀ n : ℕ, n < c → f n ≤ K
| 0 := ⟨0, λ n h, absurd h (nat.not_lt_zero n)⟩
| (c+1) := begin
  cases exists_sup_fn_fin c with K h,
  refine ⟨max K (f c), λ n h0, _⟩,
  rw [nat.lt_succ_iff, le_iff_eq_or_lt] at h0,
  rcases h0 with rfl | h0,
  exacts [le_max_right K (f n), le_trans (h n h0) (le_max_left K (f c))]
end

private lemma exists_lt_card_divisor (c : ℕ) : ∃ n : ℕ, c < n.divisors.card :=
  ⟨2 ^ c, by rw [nat.divisors_prime_pow nat.prime_two, card_map, card_range, nat.lt_succ_iff]⟩

end extra_lemmas





private def g (n : ℕ) : ℕ := (range n).sum (λ x, n / (x + 1))

@[nolint doc_blame] def f (n : ℕ) : ℚ := ((g n : ℤ) : ℚ) / ((n : ℤ) : ℚ)



private lemma g_succ (n : ℕ) : g n.succ = g n + n.succ.divisors.card :=
  by rw [nat.divisors, ← nat.cast_id (filter _ _).card, ← sum_boole, sum_Ico_eq_sum_range,
    nat.add_sub_cancel, sum_range_succ, add_comm 1 n, if_pos $ dvd_refl _, ← add_assoc,
    g, g, ← sum_add_distrib, sum_range_succ, nat.div_self n.succ_pos, add_left_inj];
  exact sum_congr rfl (λ x _, by rw [add_comm, nat.succ_div])

private lemma g_sum : ∀ n : ℕ, g n = (range n).sum (λ x, x.succ.divisors.card)
| 0 := rfl
| (n+1) := by rw [g_succ, sum_range_succ, ← g_sum]

private lemma two_le_card_divisors {n : ℕ} (h : 2 ≤ n) : 2 ≤ n.divisors.card :=
begin
  rw nat.succ_le_iff at h,
  rw ← card_doubleton (ne_of_lt h),
  refine card_le_of_subset (λ c h0, _),
  rw nat.mem_divisors; rw [mem_insert, mem_singleton] at h0,
  rcases h0 with rfl | rfl,
  exacts [⟨one_dvd n, ne_of_gt $ pos_of_gt h⟩, ⟨dvd_refl c, ne_of_gt $ pos_of_gt h⟩]
end

private lemma two_mul_lt : ∀ {n : ℕ}, 6 ≤ n → 2 * n < g n :=
begin
  refine nat.le_induction _ (λ n h h0, _),
  rw g; iterate 5 { rw sum_range_succ },
  rw [sum_range_one, zero_add]; norm_num,
  rw [mul_add_one, g_succ],
  refine add_lt_add_of_lt_of_le h0 (two_le_card_divisors _),
  exact nat.succ_le_succ (le_trans (nat.succ_le_succ $ nat.zero_le 5) h)
end

private lemma card_divisors_prime {p : ℕ} (hp : p.prime) : p.divisors.card = 2 :=
  by rw [nat.prime.divisors hp, card_doubleton hp.ne_one.symm]







/-- Final solution, part 1 -/
theorem final_solution_part1 : {n : ℕ | f n < f n.succ}.infinite :=
begin
  ---- Use unboundedness and pick a suitable number
  refine set.infinite_of_not_bdd_above _,
  rintros ⟨N, h⟩; rw mem_upper_bounds at h,
  obtain ⟨c, h0, h1⟩ : ∃ c : ℕ, N.succ < c ∧ ∀ n : ℕ, n < c → n.divisors.card < c.divisors.card :=
  begin
    obtain ⟨K, h0⟩ := exists_sup_fn_fin (λ x, x.divisors.card) N.succ.succ,
    have h1 := exists_lt_card_divisor K,
    refine ⟨nat.find h1, _, λ n h2, lt_of_le_of_lt _ (nat.find_spec h1)⟩,
    rw nat.lt_find_iff; intros n h2,
    exact not_lt_of_le (h0 n $ nat.lt_succ_of_le h2),
    replace h2 := nat.find_min h1 h2,
    rwa not_lt at h2
  end,

  ---- Change `c` to `c.succ`, and then prove that the new value of `c` works
  obtain ⟨c, rfl⟩ : ∃ n : ℕ, c = n.succ :=
    nat.exists_eq_succ_of_ne_zero (ne_of_gt $ pos_of_gt h0),
  revert h0; rw [imp_false, not_lt]; refine nat.succ_le_succ (h c _),
  rw [set.mem_set_of_eq, f, f],
  clear h; rcases eq_or_ne c 0 with rfl | h,
  rw [int.coe_nat_zero, int.cast_zero, div_zero, g, sum_range_one,
      zero_add, nat.div_one, int.coe_nat_one, int.cast_one, div_one],
  exact one_pos,
  rw [rat.div_lt_div_iff_mul_lt_mul, ← nat.cast_mul, ← nat.cast_mul,
      nat.cast_lt, g_succ, nat.mul_succ, add_mul, add_lt_add_iff_left,
      mul_comm, ← smul_eq_mul, nsmul_eq_sum_const, g_sum],
  refine sum_lt_sum_of_nonempty (nonempty_range_iff.mpr h) (λ i h0, h1 _ _),
  rw mem_range at h0; exact nat.succ_le_succ h0,
  rwa [int.coe_nat_pos, zero_lt_iff],
  rw int.coe_nat_pos; exact c.succ_pos
end



/-- Final solution, part 2 -/
theorem final_solution_part2 : {n : ℕ | f n.succ < f n}.infinite :=
begin
  ---- Use unboundedness and pick a suitable prime
  refine set.infinite_of_not_bdd_above _,
  rintros ⟨N, h⟩; rw mem_upper_bounds at h,
  rcases (max 7 (N + 2)).exists_infinite_primes with ⟨p, h1, h0⟩,
  rw max_le_iff at h1; cases h1 with h1 h2,
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n.succ := nat.exists_eq_succ_of_ne_zero h0.ne_zero,
  rw [nat.succ_le_succ_iff, nat.succ_le_iff] at h2,
  revert h2; rw [imp_false, not_lt]; apply h,

  ---- Now prove that `f(n + 1) < f(n)` (here `n + 1` is prime)
  rw nat.succ_le_succ_iff at h1,
  rw [set.mem_set_of_eq, f, f, rat.div_lt_div_iff_mul_lt_mul, ← nat.cast_mul, ← nat.cast_mul,
      nat.cast_lt, g_succ, card_divisors_prime h0, add_mul, nat.mul_succ, add_lt_add_iff_left],
  exact two_mul_lt h1,
  rw int.coe_nat_pos; exact n.succ_pos,
  rw int.coe_nat_pos; exact lt_of_lt_of_le (nat.succ_pos 5) h1
end

end IMO2006N3
end IMOSL
