import number_theory.arithmetic_function

/-! # IMO 2006 N3 -/

namespace IMOSL
namespace IMO2006N3

open finset nat.arithmetic_function

private def g (n : ℕ) : ℕ := (range n).sum (λ x, n / (x + 1))
def f (n : ℕ) : ℚ := ((g n : ℤ) : ℚ) / ((n : ℤ) : ℚ)



private lemma g_succ (n : ℕ) : g n.succ = g n + n.succ.divisors.card :=
  by rw [nat.divisors, ← nat.cast_id (filter _ _).card, ← sum_boole, sum_Ico_eq_sum_range,
    nat.add_sub_cancel, sum_range_succ, add_comm 1 n, if_pos $ dvd_refl _, ← add_assoc,
    g, g, ← sum_add_distrib, sum_range_succ, nat.div_self n.succ_pos, add_left_inj];
  exact sum_congr rfl (λ x _, by rw [add_comm, nat.succ_div])

private lemma g_sum : ∀ n : ℕ, g n = (range n.succ).sum (λ x, x.divisors.card)
| 0 := by rw [g, sum_range_zero, sum_range_one, nat.divisors_zero, card_empty]
| (n+1) := by rw [g_succ, sum_range_succ, g_sum]

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
  rw nat.succ_le_succ_iff; refine le_trans _ h,
  norm_num
end

private lemma card_divisors_prime {p : ℕ} (hp : p.prime) : p.divisors.card = 2 :=
  by rw [nat.prime.divisors hp, card_doubleton hp.ne_one.symm]







/-- Final solution, part 1 -/
theorem final_solution_part1 : {n : ℕ | f n < f n.succ}.infinite :=
begin
  suffices : {n : ℕ | 0 < n ∧ ∀ m : ℕ, m ≤ n → m.divisors.card < n.succ.divisors.card}.infinite,
  { refine set.infinite.mono _ this; clear this,
    rintros n ⟨h, h0⟩,
    rw [set.mem_set_of_eq, f, f, rat.div_lt_div_iff_mul_lt_mul],
    rotate 1,
    rwa int.coe_nat_pos,
    rw int.coe_nat_pos; exact n.succ_pos,
    rw [← nat.cast_mul, ← nat.cast_mul, nat.cast_lt, mul_comm, mul_comm (g n.succ),
        g_succ, nat.succ_mul, mul_add, add_lt_add_iff_left, g_sum, sum_range_succ',
        nat.divisors_zero, card_empty, add_zero, ← smul_eq_mul, nsmul_eq_sum_const],
    refine sum_lt_sum (λ m h1, le_of_lt (h0 _ _)) ⟨0, mem_range.mpr h, _⟩,
    rwa [nat.succ_le_iff, ← mem_range],
    rw [zero_add, nat.divisors_one, card_singleton, ← nat.succ_le_iff],
    exact two_le_card_divisors (nat.succ_le_succ h) },

  refine set.infinite_of_not_bdd_above _,
  simp_rw [bdd_above, upper_bounds, set.nonempty, not_exists, set.mem_set_of_eq, not_forall],
  intros b,
  -- We take `x` to be the minimal `nat` with `d(x + 1) > b + 1`.
  have h : ∃ y : ℕ, b + 1 < y.succ.divisors.card :=
    ⟨2 ^ (b + 1) - 1, by rw [nat.succ_eq_add_one, nat.sub_add_cancel (nat.one_le_pow' _ 1),
      nat.divisors_prime_pow nat.prime_two, card_map, card_range, nat.lt_succ_iff] ⟩,
  use nat.find h; rw [and_comm, ← and_assoc, not_le],
  refine ⟨_, λ m h0, lt_of_le_of_lt _ (nat.find_spec h)⟩,
  { rw [and_iff_left_of_imp pos_of_gt, ← not_le]; intros h0,
    replace h0 : ∃ y, y ≤ b ∧ b + 1 < y.succ.divisors.card := ⟨nat.find h, h0, nat.find_spec h⟩,
    clear h; rcases h0 with ⟨y, h, h0⟩,
    revert h; refine not_le_of_lt (nat.succ_lt_succ_iff.mp (lt_of_lt_of_le h0 _)),
    rw nat.divisors; convert finset.card_filter_le _ _,
    rw list.length_range' },
  { cases m with m m,
    rw [nat.divisors_zero, card_empty]; exact nat.zero_le _,
    have h1 := nat.find_min h h0,
    exact le_of_not_lt h1 }
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

  ---- Now prove that `f(n + 1) < f(n)`
  rw nat.succ_le_succ_iff at h1,
  rw [set.mem_set_of_eq, f, f, rat.div_lt_div_iff_mul_lt_mul],
  rw [← nat.cast_mul, ← nat.cast_mul, nat.cast_lt, mul_comm, mul_comm (g n),
      g_succ, card_divisors_prime h0, mul_add, nat.succ_mul, add_lt_add_iff_left, mul_comm],
  exact two_mul_lt h1,
  rw int.coe_nat_pos; exact n.succ_pos,
  rw int.coe_nat_pos; refine lt_of_lt_of_le _ h1,
  norm_num
end

end IMO2006N3
end IMOSL
