import number_theory.arithmetic_function

/-! # IMO 2006 N3 -/

namespace IMOSL
namespace IMO2006N3

open finset nat.arithmetic_function

private def g (n : ℕ) : ℕ := (range n).sum (λ x, n / (x + 1))



/- ## Properties of g -/
section g_prop

private lemma lem1 (n : ℕ) : g n.succ = g n + n.succ.divisors.card :=
begin
  rw [g, g, sum_range_succ, nat.div_self n.succ_pos],
  simp_rw nat.succ_div,
  rw [sum_add_distrib, add_assoc, add_right_inj, nat.divisors,
      ← nat.cast_id (filter _ _).card, ← sum_boole, sum_Ico_eq_sum_range,
      nat.add_sub_cancel, sum_range_succ, add_comm 1 n, if_pos $ dvd_refl _],
  simp_rw add_comm
end

private lemma lem2 : ∀ n : ℕ, g n = (range n.succ).sum (λ x, x.divisors.card)
| 0 := by rw [g, sum_range_zero, sum_range_one, nat.divisors_zero, card_empty]
| (n+1) := by rw [lem1, sum_range_succ, lem2]

private lemma lem3 {n : ℕ} (h : 2 ≤ n) : 2 ≤ n.divisors.card :=
begin
  rw nat.succ_le_iff at h,
  rw ← card_doubleton (ne_of_lt h),
  refine card_le_of_subset (λ c h0, _),
  rw nat.mem_divisors; rw [mem_insert, mem_singleton] at h0,
  rcases h0 with rfl | rfl,
  exacts [⟨one_dvd n, ne_of_gt $ pos_of_gt h⟩, ⟨dvd_refl c, ne_of_gt $ pos_of_gt h⟩]
end

private lemma lem4 : ∀ {n : ℕ}, 6 ≤ n → 2 * n < g n :=
begin
  refine nat.le_induction _ (λ n h h0, _),
  simp_rw [g, sum_range_succ],
  rw [sum_range_zero, zero_add, zero_add]; norm_num,
  rw [mul_add_one, lem1],
  refine add_lt_add_of_lt_of_le h0 (lem3 _),
  rw nat.succ_le_succ_iff; refine le_trans _ h,
  norm_num
end

private lemma lem5 {p : ℕ} (hp : p.prime) : p.divisors.card = 2 :=
  by rw [nat.prime.divisors hp, card_doubleton hp.ne_one.symm]

end g_prop



/-! ## Main results -/

def f (n : ℕ) : ℚ := ((g n : ℤ) : ℚ) / ((n : ℤ) : ℚ)

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
        lem1, nat.succ_mul, mul_add, add_lt_add_iff_left, lem2, sum_range_succ',
        nat.divisors_zero, card_empty, add_zero, ← smul_eq_mul, nsmul_eq_sum_const],
    refine sum_lt_sum (λ m h1, le_of_lt (h0 _ _)) ⟨0, mem_range.mpr h, _⟩,
    rwa [nat.succ_le_iff, ← mem_range],
    rw [zero_add, nat.divisors_one, card_singleton, ← nat.succ_le_iff],
    exact lem3 (nat.succ_le_succ h) },

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
  suffices : {n : ℕ | 6 ≤ n ∧ n.succ.prime}.infinite,
  { refine set.infinite.mono _ this,
    rintros n ⟨h, hp⟩,
    rw [set.mem_set_of_eq, f, f, rat.div_lt_div_iff_mul_lt_mul],
    rotate 1,
    rw int.coe_nat_pos; exact n.succ_pos,
    rw int.coe_nat_pos; exact lt_of_lt_of_le (by norm_num : 0 < 6) h,
    rw [← nat.cast_mul, ← nat.cast_mul, nat.cast_lt, mul_comm, mul_comm (g n),
        lem1, lem5 hp, mul_add, nat.succ_mul, add_lt_add_iff_left, mul_comm],
    exact lem4 h },
  
  refine set.infinite_of_not_bdd_above _,
  rintros ⟨N, h⟩; simp [mem_upper_bounds] at h,
  rcases (max 7 (N + 2)).exists_infinite_primes with ⟨⟨_, _⟩, h0, hp⟩,
  exact nat.not_prime_zero hp,
  rw [max_le_iff, nat.succ_le_succ_iff, nat.succ_le_succ_iff] at h0,
  exact not_lt_of_le (h w h0.1 hp) h0.2
end

end IMO2006N3
end IMOSL
