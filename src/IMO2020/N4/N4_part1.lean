import IMO2020.N4.N4_basic extra.number_theory.totient_bound

/-! # IMO 2020 N4, Generalized Version (Part 1) -/

namespace IMOSL
namespace IMO2020N4

open finset function

def alternating (p a b : ℕ) :=
  {i : ℕ | (F p)^[i] a < (F p^[i]) b}.infinite ∧ {i : ℕ | (F p)^[i] b < (F p^[i]) a}.infinite

def good (p : ℕ) := ∃ a b : ℕ, a.coprime p ∧ b.coprime p ∧ alternating p a b



section extra_lemmas

private lemma pow_sub_one_gcd {n : ℕ} (h : 0 < n) (k m : ℕ) :
  nat.gcd (n ^ k - 1) (n ^ m - 1) = n ^ (nat.gcd k m) - 1 :=
begin
  refine nat.gcd.induction k m (λ i, _) (λ i j hi h, _); clear k m,
  rw [pow_zero, nat.sub_self, nat.gcd_zero_left, nat.gcd_zero_left],
  rw [nat.gcd_rec i j, ← h, nat.gcd_comm],
  clear h; refine nat.modeq.gcd_eq_of_modeq (nat.modeq.add_right_cancel' 1 _),
  obtain ⟨q, r, h0, rfl⟩ : ∃ q r : ℕ, r < i ∧ q * i + r = j :=
    ⟨j / i, j % i, j.mod_lt hi, nat.div_add_mod' j i⟩,
  replace h : ∀ k : ℕ, 1 ≤ n ^ k := λ k, nat.one_le_pow k n h,
  rw [nat.mul_add_mod, nat.mod_eq_of_lt h0, nat.sub_add_cancel (h _),
      nat.sub_add_cancel (h _), ← one_mul (n ^ r), pow_add, mul_comm q, pow_mul],
  nth_rewrite 1 ← one_pow q,
  exact nat.modeq.mul_right _ (nat.modeq.pow _ (nat.modeq_sub (h i)))
end

private lemma exists_nontrivial_coprime {n : ℕ} (h : 5 ≤ n) (h0 : n ≠ 6) :
  ∃ k m : ℕ, 1 < k ∧ 1 < m ∧ k.coprime m ∧ k + m = n :=
begin
  replace h0 := extra.big_two_lt_totient' h h0,
  sorry
end

end extra_lemmas







section good_iff

variables {p : ℕ} (h : odd p)
include h

private lemma lem1_1 : ∀ {a b : ℕ}, alternating p a b → S0 h a = S0 h b :=
begin
  suffices : ∀ {a b : ℕ}, S0 h a < S0 h b → ¬alternating p a b,
  { intros a b h0,
    contrapose h0,
    rw [← ne.def, ne_iff_lt_or_gt, gt_iff_lt] at h0,
    cases h0 with h0 h0,
    exact this h0,
    rw [alternating, and_comm, ← alternating],
    exact this h0 },
  intros a b h0,
  rw [alternating, not_and_distrib],
  right; intros h1,
  obtain ⟨N, h2⟩ := eventually_F_lt_of_S0_lt h h0,
  obtain ⟨n, h3, h4⟩ := h1.exists_nat_lt N,
  exact lt_asymm (set.mem_set_of_eq.mp h3) (h2 n (le_of_lt h4))
end

private lemma lem1_2 {a b : ℕ} (h0 : alternating p a b) :
  ∃ N : ℕ, (F p)^[N] b < (F p^[N]) a ∧ (F p^[N + 1]) a < (F p^[N + 1]) b :=
begin
  cases h0 with h0 h1,
  replace h1 := h1.nonempty,
  cases h1 with K h1,
  replace h0 := h0.exists_nat_lt K,
  cases nat.find_spec h0 with h2 h3,
  have h4 := nat.find_min h0 (nat.pred_lt (ne_of_gt (pos_of_gt h3))),
  generalize_hyp : nat.find h0 = N at h2 h3 h4,
  clear h0; rw set.mem_set_of_eq at h1 h2,
  cases N with _ N,
  exfalso; exact not_lt_of_le K.zero_le h3,
  refine ⟨N, _, h2⟩,
  simp only [exists_prop, not_and, exists_prop_congr', set.mem_set_of_eq, nat.pred_succ] at h4,
  rw [nat.lt_succ_iff, le_iff_eq_or_lt] at h3,
  rcases h3 with rfl | h3,
  exact h1,
  replace h4 : ¬(F p^[N] a < (F p^[N]) b) := λ X, h4 X h3,
  rw [not_lt, le_iff_lt_or_eq] at h4,
  cases h4 with h4 h4,
  exact h4,
  replace h4 := injective.iterate (F_injective h) N h4,
  exfalso; exact ne_of_gt h1 (by rw h4)
end

private lemma lem1_3 {a b : ℕ} (h0 : b < a) (h1 : F p a < F p b) :
  ∃ k x y : ℕ, p / 2 + x < y ∧ y < p ∧ a = x + (k + 1) * p ∧ b = y + k * p :=
begin
  unfold F at h1,
  obtain ⟨m, x, h2, rfl⟩ : ∃ m x : ℕ, x < p ∧ x + m * p = a :=
    ⟨a / p, a % p, a.mod_lt h.pos, a.mod_add_div' p⟩,
  obtain ⟨k, y, h3, rfl⟩ : ∃ k y : ℕ, y < p ∧ y + k * p = b :=
    ⟨b / p, b % p, b.mod_lt h.pos, b.mod_add_div' p⟩,
  rw [nat.add_mul_mod_self_right, nat.mod_eq_of_lt h2, add_right_comm, ← two_mul,
      nat.add_mul_mod_self_right, nat.mod_eq_of_lt h3, add_right_comm, ← two_mul] at h1,
  suffices h5 : m = k + 1,
  { subst h5; refine ⟨k, x, y, _, h3, rfl, rfl⟩,
    rw [add_comm k 1, one_add_mul, ← add_assoc, add_lt_add_iff_right] at h1,
    rwa [← nat.add_mul_div_right _ _ two_pos, add_comm,
        nat.div_lt_iff_lt_mul two_pos, mul_comm, mul_comm y] },

  replace h2 : x < y :=
  begin
    rw [← add_lt_add_iff_left x, ← add_assoc, ← add_assoc, ← two_mul] at h0,
    replace h1 := lt_trans h0 h1,
    rwa [add_lt_add_iff_right, two_mul, add_lt_add_iff_right] at h1
  end,
  replace h0 := lt_trans (add_lt_add_right h2 _) h0,
  rw [add_lt_add_iff_left, mul_lt_mul_right h.pos, lt_iff_exists_add] at h0,
  rcases h0 with ⟨c, h0, rfl⟩,
  rw [add_comm k, add_mul, ← add_assoc, add_lt_add_iff_right, two_mul y] at h1,
  replace h1 := lt_trans (lt_of_le_of_lt le_add_self h1) (add_lt_add h3 h3),
  rw [← two_mul, mul_lt_mul_right h.pos, nat.lt_succ_iff] at h1,
  rw [gt_iff_lt, ← nat.succ_le_iff] at h0,
  rw le_antisymm h1 h0
end

private lemma lem1_4 : good p ↔
  (∃ x y : ℕ, x.coprime p ∧ y.coprime p ∧ p / 2 + x < y ∧ y < p ∧ S0 h x = S0 h y) :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,
  { rcases h0 with ⟨a, b, ha, hb, h0⟩,
    have h1 := lem1_1 h h0,
    obtain ⟨N, h2, h3⟩ := lem1_2 h h0,
    rw [iterate_succ', comp_app, comp_app] at h3,
    replace ha := F_iterate_coprime h ha N,
    replace hb := F_iterate_coprime h hb N,
    rw [← S0_F_iterate h N, ← S0_F_iterate h N b] at h1,
    generalize_hyp : (F p^[N]) a = c at ha h1 h2 h3,
    generalize_hyp : (F p^[N]) b = d at hb h1 h2 h3,
    obtain ⟨k, x, y, h4, h5, rfl, rfl⟩ := lem1_3 h h2 h3,
    clear h0 N a b,
    rw nat.coprime_add_mul_right_left at ha hb,
    refine ⟨x, y, ha, hb, h4, h5, _⟩,
    rw [S0_mod_p, nat.add_mul_mod_self_right, ← S0_mod_p] at h1,
    rw [h1, S0_mod_p h (y + _), nat.add_mul_mod_self_right, ← S0_mod_p] },
  { rcases h0 with ⟨x, y, hx, hy, h0, h1, h2⟩,
    have X : injective (λ k, k * order_two_mod_p h) :=
      nat.mul_left_injective (order_two_mod_p_pos h),
    refine ⟨x + p, y, _, hy, _, set.infinite_of_injective_forall_mem X _⟩,
    rwa nat.coprime_add_self_left,
    refine set.infinite_of_injective_forall_mem (injective.comp (add_left_injective 1) X) _,
    intros k; simp only [comp_app, set.mem_set_of_eq],
    rw [F_iterate_S, S_mul_order_add, F_iterate_S, S_mul_order_add, S0_mod_p,
        nat.add_mod_right, ← S0_mod_p, h2, add_left_comm, add_left_comm y,
        add_lt_add_iff_left, S_one, S_one, nat.add_mod_right, nat.mod_eq_of_lt h1,
        ← two_mul, add_right_comm, nat.mod_eq_of_lt, ← two_mul],
    rwa [← nat.add_mul_div_left _ _ two_pos, add_comm,
        nat.div_lt_iff_lt_mul two_pos, mul_comm y 2] at h0,
    exact lt_trans (lt_of_le_of_lt le_add_self h0) h1,
    intros k; simp only [comp_app, set.mem_set_of_eq],
    rw [F_iterate_S, S_mul_order, F_iterate_S, S_mul_order, S0_mod_p h (x + p),
        nat.add_mod_right, ← S0_mod_p, h2, add_lt_add_iff_right],
    exact lt_of_lt_of_le h1 le_add_self }
end

end good_iff





section computation

private lemma lem2_1 {p : ℕ} (h : odd p) (h0 : ∀ k : ℕ, p ≠ 2 ^ k - 1) : good p :=
begin
  rw lem1_4 h,
  obtain ⟨c, h1, h2⟩ : ∃ c : ℕ, p ≤ 2 ^ c ∧ ∀ b : ℕ, b < c → 2 ^ b < p :=
  begin
    have X : ∃ a : ℕ, p ≤ 2 ^ a := ⟨p, le_of_lt p.lt_two_pow⟩,
    refine ⟨nat.find X, nat.find_spec X, λ b h1, _⟩,
    replace h1 := nat.find_min X h1,
    rw ← not_le; exact h1
  end,

  cases c with _ c,
  { rw [pow_zero, le_iff_lt_or_eq, nat.lt_one_iff] at h1,
    rcases h1 with rfl | rfl,
    exfalso; exact h0 0 (by rw pow_zero),
    exfalso; exact h0 1 (by rw pow_one) },
  replace h2 := h2 c c.lt_succ_self,
  refine ⟨1, 2 ^ c, p.coprime_one_left, (two_coprime_p h).pow_left c,
    _, h2, by rw [← mul_one (2 ^ c), S0_two_pow_mul]⟩,
  rw [← nat.add_mul_div_right _ _ two_pos, nat.div_lt_iff_lt_mul two_pos, ← pow_succ', one_mul],
  replace h2 : even (2 ^ c.succ) := nat.even_pow.mpr ⟨even_two, c.succ_ne_zero⟩,
  rw nat.odd_iff_not_even at h,
  rw [le_iff_eq_or_lt, ← nat.add_one_le_iff, le_iff_eq_or_lt, ← nat.add_one_le_iff] at h1,
  rcases h1 with rfl | h1 | h1,
  exfalso; exact h h2,
  exfalso; refine h0 c.succ _,
  rw [← h1, nat.add_sub_cancel],
  rw le_iff_lt_or_eq at h1; cases h1 with h1 h1,
  exact h1,
  rw [← h1, add_assoc, nat.even_add, iff_true_intro even_two, iff_true] at h2,
  exfalso; exact h h2
end



private lemma lem2_2 {k : ℕ} (h : 5 ≤ k) : good (2 ^ k - 1) :=
begin
  have X : odd (2 ^ k - 1) :=
  begin
    rw [nat.odd_iff_not_even, ← nat.even_add_one, nat.sub_add_cancel, nat.even_pow'],
    exact even_two,
    rintros rfl; revert h; norm_num,
    exact nat.one_le_pow k 2 two_pos
  end,
  rw lem1_4 X; rcases eq_or_ne k 6 with rfl | h0,
  refine ⟨5, 2 ^ 3 * 5, _, _, _, _, by rw S0_two_pow_mul⟩; norm_num,
  replace h0 := exists_nontrivial_coprime h h0,
  rcases h0 with ⟨c, d, h0, h1, h2, rfl⟩,
  replace h : nat.coprime (2 ^ c - 1) (2 ^ (c + d) - 1) :=
    by unfold nat.coprime at h2 ⊢;
      rw [pow_sub_one_gcd two_pos, nat.gcd_self_add_right, h2, pow_one],
  refine ⟨2 ^ c - 1, 2 ^ d * (2 ^ c - 1), h, _, _, _, by rw S0_two_pow_mul⟩,
  exact nat.coprime.mul (nat.coprime.pow_left _ (two_coprime_p X)) h,
  { clear h2 X h; have X : 1 ≤ 2 := one_le_two,
    rw ← nat.succ_le_iff at h0 h1,
    replace h0 := pow_le_pow X h0,
    replace h1 := pow_le_pow X h1,
    rw pow_add; clear X,
    generalize_hyp : 2 ^ c = M at h0 ⊢,
    generalize_hyp : 2 ^ d = N at h1 ⊢,
    cases M with _ M,
    exfalso; revert h0; norm_num,
    cases N with _ N,
    exfalso; revert h1; norm_num,
    norm_num at h0 h1; rw nat.succ_le_succ_iff at h0 h1,
    rw [nat.succ_sub_one, nat.succ_mul, nat.mul_succ, nat.succ_mul, add_lt_add_iff_right,
        nat.add_sub_assoc (nat.succ_le_succ (zero_le N)), nat.succ_sub_one,
        nat.div_lt_iff_lt_mul two_pos, mul_comm, mul_two, add_assoc, add_lt_add_iff_left],
    
    -- This could be made better, I do not have the time to think how
    cases M with _ M,
    exfalso; revert h0; norm_num,
    cases N with _ N,
    exfalso; revert h1; norm_num,
    rw [nat.mul_succ, nat.succ_mul, nat.succ_eq_one_add,
        add_lt_add_iff_right, add_lt_add_iff_right],
    rw nat.succ_le_succ_iff at h0 h1,
    exact lt_of_lt_of_le (by norm_num : 1 < 2 * 2) (nat.mul_le_mul h1 h0) },
  { rw [nat.mul_sub_left_distrib, mul_one, ← pow_add, add_comm, tsub_lt_tsub_iff_left_of_le_of_le],
    exact nat.one_lt_two_pow d (lt_trans one_pos h1),
    rw pow_add; exact le_mul_of_one_le_left' (nat.one_le_pow c 2 two_pos),
    exact nat.one_le_pow (c + d) 2 two_pos }
end



private lemma lem2_3 : ¬good 1 :=
begin
  rw lem1_4 odd_one; simp only [not_exists],
  rintros x y ⟨-, -, h, h0, -⟩,
  rw nat.lt_one_iff at h0,
  exact ne_of_gt (pos_of_gt h) h0
end

private lemma lem2_4 : ¬good 3 :=
begin
  have h : odd 3 := ⟨1, by rw [bit1, mul_one]⟩,
  rw lem1_4 h; simp only [not_exists],
  rintros x y ⟨h0, -, h1, h2, -⟩,
  rw [nat.bit1_div_two, add_comm, ← nat.add_one_le_iff, add_assoc, le_iff_exists_add] at h1,
  rcases h1 with ⟨c, rfl⟩,
  rw [nat.lt_succ_iff, add_right_comm, add_le_iff_nonpos_left, le_zero_iff, add_eq_zero_iff] at h2,
  rcases h2 with ⟨rfl, rfl⟩,
  rw [nat.coprime_zero_left, nat.bit1_eq_one] at h0,
  exact one_ne_zero h0
end



private lemma lem2_5 : ¬good 7 :=
begin
  have h : odd 7 := ⟨3, by rw [bit1, bit0, two_mul]⟩,
  rw lem1_4 h; simp only [not_exists],
  rintros x y ⟨h0, h1, h2, h3, h4⟩,

  -- We first claim that the order of 2 mod 7 is 3
  have X : order_two_mod_p h = 3 :=
  begin
    rw [order_two_mod_p, nat.find_eq_iff],
    unfold nat.modeq; norm_num,
    intros n hn hn0; rw nat.lt_succ_iff at hn,
    rw [nat.mod_eq_of_lt, pow_eq_one_iff],
    norm_num,
    exact ne_of_gt hn0,
    exact lt_of_le_of_lt (pow_le_pow one_le_two hn) (by norm_num)
  end,

  -- Unfold the sum in h4
  rw [S0, S0, X, S, S] at h4,
  repeat { rw sum_range_succ at h4 },
  rw [sum_range_zero, zero_add, sum_range_zero, zero_add] at h4,

  -- Next we set up the inequalities: 1 ≤ x and x + 4 ≤ y ≤ 6
  rw nat.lt_succ_iff at h3,
  rw [add_comm, ← nat.add_one_le_iff, add_assoc] at h2; norm_num at h2,
  replace h0 : 1 ≤ x := begin
    rw [nat.succ_le_iff, zero_lt_iff]; rintros rfl,
    rw [nat.coprime_zero_left, nat.bit1_eq_one] at h0,
    exfalso; exact nat.bit1_ne_zero _ h0
  end,

  -- 1 ≤ x and x + 4 ≤ y ≤ 6 implies (x, y) = (1, 5), (1, 6), (2, 6).
  -- Unfold each of these cases
  rw [le_iff_eq_or_lt, ← nat.succ_le_iff] at h0,
  rcases h0 with rfl | h0,
  norm_num at h4,
  rw [le_iff_eq_or_lt, ← nat.succ_le_iff] at h2,
  norm_num at h2; rcases h2 with rfl | h2,
  norm_num at h4,
  rw le_antisymm h3 h2 at h4; norm_num at h4,
  have h5 := le_trans (add_le_add_right h0 _) h2,
  norm_num at h5; replace h5 := le_antisymm h3 h5,
  rw h5 at h2 h4,
  change (x + 4 ≤ 2 + 4) at h2,
  rw add_le_add_iff_right at h2,
  rw le_antisymm h2 h0 at h4,
  norm_num at h4
end



private lemma lem2_6_1 : odd 15 :=
  ⟨7, by rw [bit1, bit0, two_mul]⟩

private lemma lem2_6_2 : order_two_mod_p lem2_6_1 = 4 :=
begin
  rw [order_two_mod_p, nat.find_eq_iff],
  unfold nat.modeq; norm_num,
  intros n hn hn0; rw nat.lt_succ_iff at hn,
  rw [nat.mod_eq_of_lt, pow_eq_one_iff],
  norm_num,
  exact ne_of_gt hn0,
  exact lt_of_le_of_lt (pow_le_pow one_le_two hn) (by norm_num)
end

private lemma lem2_6_3 {x : ℕ} (h : x.coprime 15) (h0 : x < 15) :
  (x ∈ ({1, 2, 4, 8} : finset ℕ) ∧ S0 lem2_6_1 x = 15) ∨
  (x ∈ ({7, 11, 13, 14} : finset ℕ) ∧ S0 lem2_6_1 x = 45) :=
begin
 unfold S0 S; rw lem2_6_2,
 rw ← mem_range at h0; revert h,
 repeat { rw sum_range_succ },
 rw [sum_range_zero, zero_add],
 -- There are better ways, certainly...
 -- To be replaced, it works now but...
 sorry
 -- fin_cases h0; norm_num
end

private lemma lem2_6_4 {x y : ℕ} (h : x.coprime 15) (h0 : y.coprime 15)
  (h1 : x < 15) (h2 : y < 15) (h3 : S0 lem2_6_1 x = S0 lem2_6_1 y) :
  y ≤ x + 7 :=
begin
  /-
  replace h1 := lem2_6_3 h h1,
  replace h2 := lem2_6_3 h0 h2,
  rcases h1 with ⟨h11, h12⟩ | ⟨h11, h12⟩,
  -/
  sorry
end
  

private lemma lem2_250 : ¬good 15 :=
begin
  /-
  have h : odd 15 := ⟨7, by rw [bit1, bit0, two_mul]⟩,
  rw lem1_4 h; simp only [not_exists],
  rintros x y ⟨h0, h1, h2, h3, h4⟩,

  -- We first claim that the order of 2 mod 15 is 4
  have X : order_two_mod_p h = 4 :=
  begin
    rw [order_two_mod_p, nat.find_eq_iff],
    unfold nat.modeq; norm_num,
    intros n hn hn0; rw nat.lt_succ_iff at hn,
    rw [nat.mod_eq_of_lt, pow_eq_one_iff],
    norm_num,
    exact ne_of_gt hn0,
    exact lt_of_le_of_lt (pow_le_pow one_le_two hn) (by norm_num)
  end,

  -- Unfold the sum in h4
  rw [S0, S0, X, S, S] at h4,
  repeat { rw sum_range_succ at h4 },
  rw [sum_range_zero, zero_add, sum_range_zero, zero_add] at h4,

  -- ...
  -/
  sorry
end

private lemma lem2_300 {p : ℕ} (h : p ∈ ({1, 3, 7, 15} : finset ℕ)) : ¬good p :=
begin
  simp only [finset.mem_insert, finset.mem_singleton] at h,
  rcases h with rfl | rfl | rfl | rfl,
  exacts [lem2_3, lem2_4, lem2_5, lem2_250]
end

end computation







/-- Final solution -/
theorem final_solution_part1' {p : ℕ} (h : odd p) :
  good p ↔ p ∉ ({1, 3, 7, 15} : finset ℕ) :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,
  contrapose! h0; exact lem2_300 h0,
  by_cases h1 : ∀ k : ℕ, p ≠ 2 ^ k - 1,
  exact lem2_1 h h1,
  simp only [not_forall, not_not] at h1,
  rcases h1 with ⟨k, rfl⟩,
  refine lem2_2 (le_of_not_lt _),
  contrapose! h0; simp only [finset.mem_insert, finset.mem_singleton],
  repeat { rw [nat.lt_succ_iff, le_iff_lt_or_eq] at h0 },
  repeat { rw [or_assoc] at h0 },
  rcases h0 with h0 | rfl | h0,
  exfalso; exact not_le_of_lt h0 k.zero_le,
  rw [pow_zero, nat.sub_self, nat.odd_iff_not_even] at h,
  exfalso; exact h even_zero,
  rcases h0 with rfl | rfl | rfl | rfl; norm_num
end

end IMO2020N4
end IMOSL