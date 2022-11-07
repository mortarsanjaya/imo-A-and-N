import IMO2020.N4.N4_basic extra.number_theory.totient_bound

/-! # IMO 2020 N4, Generalized Version (Part 1) -/

namespace IMOSL
namespace IMO2020N4

open finset function

def alternating (p a b : ℕ) :=
  {i : ℕ | (F p)^[i] a < (F p^[i]) b}.infinite ∧ {i : ℕ | (F p)^[i] b < (F p^[i]) a}.infinite

def good (p : ℕ) := ∃ a b : ℕ, a.coprime p ∧ b.coprime p ∧ alternating p a b







/-! # Some extra lemmas not-so-related to the problem -/
section extra_lemmas

private lemma pow_sub_one_gcd (n k m : ℕ) :
  nat.gcd (n ^ k - 1) (n ^ m - 1) = n ^ (nat.gcd k m) - 1 :=
begin
  ---- The case `n = 0` is about the implementation of `nat.sub`
  rcases n.eq_zero_or_pos with rfl | h,
  suffices : ∀ n : ℕ, 0 ^ n - 1 = 0,
    rw [this, this, this, nat.gcd_self],
  intros n; rcases n.eq_zero_or_pos with rfl | h,
  rw [pow_zero, nat.sub_self],
  rw zero_pow h,

  ---- This is the real case: gcd induction is a standard way
  refine nat.gcd.induction k m (λ i, _) (λ i j hi h, _); clear k m,
  rw [pow_zero, nat.sub_self, nat.gcd_zero_left, nat.gcd_zero_left],
  rw [nat.gcd_rec i j, ← h, nat.gcd_comm]; clear h,
  refine nat.modeq.gcd_eq_of_modeq (nat.modeq.add_right_cancel' 1 _),
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
  unfold nat.totient at h0,
  sorry
end

private lemma Mersenne_odd {k : ℕ} (h : 0 < k) : odd (2 ^ k - 1) :=
begin
  rw [nat.odd_iff_not_even, ← nat.even_add_one,
      nat.sub_add_cancel (nat.one_le_pow k 2 two_pos), nat.even_pow' (ne_of_gt h)],
  exact even_two
end

private lemma order_two_mod_Mersenne {k : ℕ} (h : odd (2 ^ k - 1)) :
  order_two_mod_p h = k :=
begin
  have X : ∀ m : ℕ, 1 ≤ 2 ^ m := λ m, nat.one_le_pow m 2 two_pos,
  unfold order_two_mod_p; apply le_antisymm,
  rw nat.find_le_iff; refine ⟨k, le_refl k, _, nat.modeq_sub (X k)⟩,
  rw zero_lt_iff; rintros rfl,
  rw [pow_zero, nat.sub_self, nat.odd_iff_not_even] at h,
  exact h even_zero,
  rw nat.le_find_iff; rintros m h0 ⟨h1, h2⟩,
  rw [nat.modeq.comm, nat.modeq_iff_dvd' (X m)] at h2,
  revert h2; refine nat.not_dvd_of_pos_of_lt _ _,
  rw tsub_pos_iff_lt; exact nat.one_lt_pow m 2 h1 one_lt_two,
  rw tsub_lt_tsub_iff_right (X m); exact pow_lt_pow one_lt_two h0
end

private lemma sum_two_pow (k : ℕ) : (range k).sum (λ i, 2 ^ i) = 2 ^ k - 1 :=
  by rw [← geom_sum_mul_add 1 k, nat.add_sub_cancel, mul_one]

private lemma S0_Mersenne_one {k : ℕ} (h : odd (2 ^ k - 1)) (h0 : 1 < k) :
  S0 h 1 = 2 ^ k - 1 :=
begin
  rw [S0, order_two_mod_Mersenne, S],
  nth_rewrite 0 ← sum_two_pow,
  refine sum_congr rfl (λ i h1, _),
  rw [mul_one, nat.mod_eq_of_lt],
  obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero (ne_of_gt (lt_trans one_pos h0)),
  rw [mem_range, nat.lt_succ_iff] at h1,
  rw [lt_tsub_iff_right, pow_succ, two_mul],
  refine add_lt_add_of_le_of_lt (nat.pow_le_pow_of_le_right two_pos h1) _,
  rw nat.succ_lt_succ_iff at h0; exact nat.one_lt_two_pow m h0
end

end extra_lemmas







/-! ## Equivalent criterion for `p` to be good -/
section good_iff

variables {p : ℕ} (h : odd p)
include h

private lemma alternating_S0_eq {a b : ℕ} (h0 : alternating p a b) : S0 h a = S0 h b :=
begin
  contrapose h0; rw [alternating, not_and_distrib],
  rw [← ne.def, ne_iff_lt_or_gt, gt_iff_lt] at h0,
  wlog h0 : S0 h a < S0 h b := h0 using [a b, b a],
  replace h0 := eventually_F_lt_of_S0_lt h h0,
  cases h0 with N h0,
  right; intros h1,
  replace h1 := h1.exists_nat_lt N,
  rcases h1 with ⟨n, h1, h2⟩,
  rw set.mem_set_of_eq at h1,
  exact lt_asymm h1 (h0 n (le_of_lt h2))
end

private lemma alternating_consecutive {a b : ℕ} (h0 : alternating p a b) :
  ∃ N : ℕ, (F p)^[N] b < (F p^[N]) a ∧ (F p^[N + 1]) a < (F p^[N + 1]) b :=
begin
  ---- First find some `K` with `F_p^K(b) < F_p^K(a)`.
  cases h0 with h0 h1,
  replace h1 := h1.nonempty,
  cases h1 with K h1,

  ---- Next find the minimum `N > K` with `F_p^N(a) < F_p^N(b)`.
  replace h0 := h0.exists_nat_lt K,
  cases nat.find_spec h0 with h2 h3,
  have h4 := nat.find_min h0 (nat.pred_lt (ne_of_gt (pos_of_gt h3))),
  generalize_hyp : nat.find h0 = N at h2 h3 h4,
  clear h0; rw set.mem_set_of_eq at h1 h2,
  simp only [exists_prop, not_and, exists_prop_congr', set.mem_set_of_eq, nat.pred_succ] at h4,

  ---- We have `N > 0`. Replace `N` with `N + 1` and show that `N` is the desired index.
  cases N with _ N,
  exfalso; exact not_lt_of_le K.zero_le h3,
  refine ⟨N, _, h2⟩; clear h2,
  contrapose! h4,
  rw nat.pred_succ; split,
  { refine ne.lt_of_le _ h4,
    clear h4; intros h4,
    replace h4 := injective.iterate (F_injective h) N h4,
    subst h4; exact ne_of_gt h1 rfl },
  { rw nat.lt_succ_iff at h3,
    refine ne.lt_of_le _ h3,
    clear h3; intros h3,
    subst h3; exact not_le_of_lt h1 h4 }
end

private lemma F_switch_sign {a b : ℕ} (h0 : b < a) (h1 : F p a < F p b) :
  ∃ k x y : ℕ, p / 2 + x < y ∧ y < p ∧ a = x + (k + 1) * p ∧ b = y + k * p :=
begin
  ---- First expand `a = kp + x` and `b = mp + y`
  unfold F at h1,
  obtain ⟨m, x, h2, rfl⟩ : ∃ m x : ℕ, x < p ∧ x + m * p = a :=
    ⟨a / p, a % p, a.mod_lt h.pos, a.mod_add_div' p⟩,
  obtain ⟨k, y, h3, rfl⟩ : ∃ k y : ℕ, y < p ∧ y + k * p = b :=
    ⟨b / p, b % p, b.mod_lt h.pos, b.mod_add_div' p⟩,
  rw [nat.add_mul_mod_self_right, nat.mod_eq_of_lt h2, add_right_comm, ← two_mul,
      nat.add_mul_mod_self_right, nat.mod_eq_of_lt h3, add_right_comm, ← two_mul] at h1,
  
  ---- Reduce to showing that `m = k + 1`
  suffices h5 : m = k + 1,
  { subst h5; refine ⟨k, x, y, _, h3, rfl, rfl⟩,
    rw [add_comm k 1, one_add_mul, ← add_assoc, add_lt_add_iff_right] at h1,
    rwa [← nat.add_mul_div_right _ _ two_pos, add_comm,
         nat.div_lt_iff_lt_mul two_pos, mul_comm, mul_comm y] },

  ---- Obtain `x < y`
  replace h2 : x < y :=
  begin
    rw [← add_lt_add_iff_left x, ← add_assoc, ← add_assoc, ← two_mul] at h0,
    replace h1 := lt_trans h0 h1,
    rwa [add_lt_add_iff_right, two_mul, add_lt_add_iff_right] at h1
  end,

  ---- Finishing
  replace h0 := lt_trans (add_lt_add_right h2 _) h0,
  rw [add_lt_add_iff_left, mul_lt_mul_right h.pos, lt_iff_exists_add] at h0,
  rcases h0 with ⟨c, h0, rfl⟩,
  rw [add_comm k, add_mul, ← add_assoc, add_lt_add_iff_right, two_mul y] at h1,
  replace h1 := lt_trans (lt_of_le_of_lt le_add_self h1) (add_lt_add h3 h3),
  rw [← two_mul, mul_lt_mul_right h.pos, nat.lt_succ_iff] at h1,
  rw [gt_iff_lt, ← nat.succ_le_iff] at h0,
  rw le_antisymm h1 h0
end

/-- Theorem 2 in the .tex file -/
private theorem good_iff' : good p ↔
  (∃ x y : ℕ, x.coprime p ∧ y.coprime p ∧ p / 2 + x < y ∧ y < p ∧ S0 h x = S0 h y) :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,

  ---- Left-to-right direction
  { -- Replace `a` and `b` with `c` and `d` with `d < c` and `F_p(c) < F_p(d)`
    rcases h0 with ⟨a, b, ha, hb, h0⟩,
    have h2 := alternating_S0_eq h h0,
    replace h0 := alternating_consecutive h h0,
    rcases h0 with ⟨N, h0, h1⟩,
    rw [iterate_succ', comp_app, comp_app] at h1,
    replace ha := F_iterate_coprime h ha N,
    replace hb := F_iterate_coprime h hb N,
    rw [← S0_F_iterate h N, ← S0_F_iterate h N b] at h2,
    generalize_hyp : (F p^[N]) a = c at ha h2 h0 h1,
    generalize_hyp : (F p^[N]) b = d at hb h2 h0 h1,

    ---- Finishing using the previous lemma
    replace h1 := F_switch_sign h h0 h1,
    clear h0 a b,
    rcases h1 with ⟨k, x, y, h0, h1, rfl, rfl⟩,
    rw nat.coprime_add_mul_right_left at ha hb,
    rw [S0_mod_p, nat.add_mul_mod_self_right, ← S0_mod_p,
        S0_mod_p h (y + _), nat.add_mul_mod_self_right, ← S0_mod_p] at h2,
    exact ⟨x, y, ha, hb, h0, h1, h2⟩ },

  ---- Right-to-left direction
  { rcases h0 with ⟨x, y, hx, hy, h0, h1, h2⟩,
    refine ⟨x + p, y, by rwa nat.coprime_add_self_left, hy, _⟩,
    have X : injective (λ k, k * order_two_mod_p h) :=
      nat.mul_left_injective (order_two_mod_p_pos h),
     clear hx hy; split,

    -- `F_p^{kT + 1}(x + p) < F_p^{kT + 1}(y)` for all `k ≥ 0`
    { refine set.infinite_of_injective_forall_mem (injective.comp (add_left_injective 1) X) _,
      clear X; intros k; simp only [comp_app, set.mem_set_of_eq],
      have h3 : x < p := lt_trans (lt_of_le_of_lt le_add_self h0) h1,
      rw [← nat.add_mul_div_left _ _ two_pos, add_comm, nat.div_lt_iff_lt_mul two_pos] at h0,
      rwa [F_iterate_mul_ord_add, F_iterate_mul_ord_add, S_one, S_one, add_right_comm, S0_mod_p,
           nat.add_mod_right, nat.mod_eq_of_lt h3, add_right_comm x, add_right_comm _ (k * _),
           h2, add_lt_add_iff_right, nat.mod_eq_of_lt h1, ← two_mul, ← mul_two] },

    -- `F_p^{kT}(x + p) > F_p^{kT}(y)` for all `k ≥ 0`
    { refine set.infinite_of_injective_forall_mem X _,
      clear X h0; intros k,
      rw [set.mem_set_of_eq, F_iterate_mul_ord, F_iterate_mul_ord, S0_mod_p h (x + p),
          nat.add_mod_right, ← S0_mod_p, h2, add_lt_add_iff_right],
      exact lt_of_lt_of_le h1 le_add_self } }
end

end good_iff







/-! # Computations determining goodness -/
section computation

private lemma not_Mersenne_good {p : ℕ} (h : odd p) (h0 : ∀ k : ℕ, p ≠ 2 ^ k - 1) : good p :=
begin
  ---- Find the minimal `c` with `p ≤ 2^c`, and replace `c` with `c + 1`, as `c > 0`
  rw good_iff' h,
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
  
  ---- Reduce to proving `p + 2 < 2^{c + 1}` and then proceed
  refine ⟨1, 2 ^ c, p.coprime_one_left, (two_coprime_p h).pow_left c,
    _, h2 c c.lt_succ_self, by rw [← mul_one (2 ^ c), S0_two_pow_mul]⟩,
  rw [← nat.add_mul_div_right _ _ two_pos, nat.div_lt_iff_lt_mul two_pos, ← pow_succ', one_mul],
  contrapose! h0; use c.succ,
  replace h2 : even (2 ^ c.succ) := nat.even_pow.mpr ⟨even_two, c.succ_ne_zero⟩,
  rw nat.odd_iff_not_even at h,
  rw [le_iff_eq_or_lt, ← nat.add_one_le_iff] at h1,
  rcases h1 with rfl | h1,
  exfalso; exact h h2,
  rw [le_iff_eq_or_lt, nat.lt_succ_iff] at h0,
  cases h0 with h0 h0,
  rw [h0, nat.even_add, iff_true_intro even_two, iff_true] at h2,
  exfalso; exact h h2,
  rw [le_antisymm h0 h1, nat.add_sub_cancel]
end

private lemma Mersenne_big_good {k : ℕ} (h : 5 ≤ k) : good (2 ^ k - 1) :=
begin
  ---- First, solve the case `k = 6`.
  have X : odd (2 ^ k - 1) := Mersenne_odd (lt_of_lt_of_le (by norm_num : 0 < 5) h),
  rw good_iff' X; rcases eq_or_ne k 6 with rfl | h0,
  refine ⟨5, 2 ^ 3 * 5, _, _, _, _, by rw S0_two_pow_mul⟩; norm_num,

  ---- Now focus on the case `k ≠ 6`. Reduce to the main inequality.
  replace h0 := exists_nontrivial_coprime h h0,
  rcases h0 with ⟨c, d, h0, h1, h2, rfl⟩,
  replace h : nat.coprime (2 ^ c - 1) (2 ^ (c + d) - 1) :=
    by unfold nat.coprime at h2 ⊢; rw [pow_sub_one_gcd, nat.gcd_self_add_right, h2, pow_one],
  refine ⟨2 ^ c - 1, 2 ^ d * (2 ^ c - 1), h, ((two_coprime_p X).pow_left _).mul h, _⟩,
  rw and_comm; refine ⟨⟨_, by rw S0_two_pow_mul⟩, _⟩,
  rw [nat.mul_sub_left_distrib, mul_one, ← pow_add, add_comm],
  exact tsub_lt_tsub_left_of_le (nat.pow_le_pow_of_le_right two_pos le_add_self)
    (nat.one_lt_two_pow d (lt_trans one_pos h1)),
  
  ---- Now focus on the main inequality. Start with some clean-ups and reductions
  replace X : 1 ≤ 2 := one_le_two,
  rw ← nat.succ_le_iff at h0 h1,
  replace h0 := pow_le_pow X h0,
  replace h1 := pow_le_pow X h1,
  rw pow_add,
  generalize_hyp : 2 ^ c = M at h0 ⊢,
  generalize_hyp : 2 ^ d = N at h1 ⊢,
  norm_num at h0 h1,
  replace h : ∀ n : ℕ, 4 ≤ n → ∃ m : ℕ, n = m.succ :=
    λ n Y, nat.exists_eq_succ_of_ne_zero (ne_of_gt (lt_of_lt_of_le four_pos Y)),
  obtain ⟨m, rfl⟩ := h M h0,
  obtain ⟨n, rfl⟩ := h N h1,
  clear X h h2,
  rw nat.succ_le_succ_iff at h0 h1,

  ---- Finishing
  rw [nat.succ_sub_one, nat.succ_mul, nat.mul_succ, nat.succ_mul, add_lt_add_iff_right,
      nat.succ_eq_add_one, ← add_assoc, nat.add_sub_cancel, nat.div_lt_iff_lt_mul two_pos,
      mul_comm, mul_two, add_assoc, add_lt_add_iff_left],
  have h : ∀ n : ℕ, 3 ≤ n → ∃ m : ℕ, n = m.succ :=
    λ n Y, nat.exists_eq_succ_of_ne_zero (ne_of_gt (lt_of_lt_of_le three_pos Y)),
  obtain ⟨M, rfl⟩ := h m h0,
  obtain ⟨N, rfl⟩ := h n h1,
  rw [nat.succ_le_succ_iff, nat.succ_le_iff] at h0 h1,
  rw [nat.mul_succ, nat.succ_mul, nat.succ_eq_one_add,
      add_lt_add_iff_right, add_lt_add_iff_right, ← one_mul 1],
  exact nat.mul_lt_mul h1 (le_of_lt h0) one_pos
end



private lemma Mersenne_small_bad {k : ℕ} (h : 0 < k) (h0 : k < 5) : ¬good (2 ^ k - 1) :=
begin
  replace h := nat.exists_eq_succ_of_ne_zero (ne_of_gt h),
  rcases h with ⟨k, rfl⟩,
  rw [nat.succ_lt_succ_iff, nat.lt_succ_iff, le_iff_lt_or_eq, nat.lt_succ_iff,
      le_iff_lt_or_eq, or_assoc, nat.lt_succ_iff, le_iff_lt_or_eq, nat.lt_one_iff] at h0,
  have X : odd (2 ^ k.succ - 1) := Mersenne_odd k.succ_pos,
  rw good_iff' X; rcases h0 with h0 | h0,

  ---- Easy case: `k = 0` and `k = 1`
  { rintros ⟨x, y, h, -, h1, h2, -⟩,
    rcases h0 with rfl | rfl,
    rw [pow_one, bit0, nat.add_sub_cancel, nat.lt_one_iff] at h2,
    exact ne_of_gt (pos_of_gt h1) h2,
    norm_num at h1 h2 h,
    rw [← nat.add_one_le_iff, le_iff_exists_add] at h1,
    rcases h1 with ⟨c, rfl⟩,
    rw [add_right_comm, nat.succ_lt_succ_iff, add_assoc, add_comm,
        nat.succ_lt_succ_iff, nat.lt_one_iff, add_eq_zero_iff] at h2,
    rcases h2 with ⟨rfl, -⟩,
    rw nat.coprime_zero_left at h,
    revert h; norm_num },

  ---- Hard case: `k = 2` and `k = 3`
  /-
  { -- Setup
    have X0 : S0 X 1 = 2 ^ k.succ - 1 :=
      S0_Mersenne_one X (by rcases h0 with rfl | rfl; norm_num),
    have X1 : S0 X (2 ^ k.succ - 1 - 1) = k * (2 ^ k.succ - 1) :=
    begin
      S0_p_dvd_add X,
    end,
    replace h0 : 2 ^ k.succ - 1 = 7 ∨ 2 ^ k.succ - 1 = 15 :=
      by rcases h0 with rfl | rfl; norm_num,
    generalize_hyp hn : 2 ^ k.succ - 1 = n at X X0 h0 ⊢,

    -- Reduction
    suffices : ∀ a : ℕ, a.coprime n → a < n → ∃ i : ℕ, i < k.succ ∧ a = 2 ^ i ∨ a = n - 2 ^ i,
    { rintros ⟨x, y, h1, h2, h3, h4, h5⟩,
      replace h1 := this x h1 (lt_trans (lt_of_le_of_lt le_add_self h3) h4),
      replace h2 := this y h2 h4,
    },
    sorry }
  -/
  sorry
end

private theorem final_solution_part1' {p : ℕ} (h : odd p) :
  good p ↔ ¬∃ (k : ℕ) (_ : k ∈ range 4), 2 ^ k.succ - 1 = p :=
begin
  by_cases h0 : ∀ k : ℕ, p ≠ 2 ^ k - 1,
  
  ---- Case 1: `p` is not Mersenne
  { rw [iff_true_intro (not_Mersenne_good h h0), true_iff],
    rintros ⟨k, -, rfl⟩; exact h0 k.succ rfl },

  simp only [not_forall, not_not] at h0,
  rcases h0 with ⟨k, rfl⟩,
  cases k with _ k,
  rw [pow_zero, nat.sub_self, nat.odd_iff_not_even] at h,
  exfalso; exact h even_zero,
  by_cases h0 : 5 ≤ k.succ,

  ---- Case 2: `p = 2^{k + 1} - 1`, `k + 1 ≥ 5`
  { rw [iff_true_intro (Mersenne_big_good h0), true_iff],
    rintros ⟨m, h1, h2⟩,
    have X : ∀ n : ℕ, 1 ≤ 2 ^ n := λ n, nat.one_le_pow n 2 two_pos,
    rw [← add_left_inj 1, nat.sub_add_cancel (X _), nat.sub_add_cancel (X _)] at h2,
    replace h2 := nat.succ_injective (nat.pow_right_injective (le_refl 2) h2),
    rw [← h2, nat.succ_le_succ_iff] at h0,
    rw mem_range at h1; exact not_lt_of_le h0 h1 },
  
  ---- Case 3: `p = 2^k - 1`, `k < 5`
  { rw not_le at h0,
    rw [iff_false_intro (Mersenne_small_bad k.succ_pos h0), false_iff, not_not],
    rw [nat.succ_lt_succ_iff, ← mem_range] at h0,
    exact ⟨k, h0, rfl⟩ }
end

end computation







/-- Final solution, part 1 -/
theorem final_solution_part1 {p : ℕ} (h : odd p) :
  good p ↔ p ∉ ({1, 3, 7, 15} : finset ℕ) :=
  by rw [final_solution_part1' h, not_iff_not, ← mem_image]; congr'

end IMO2020N4
end IMOSL