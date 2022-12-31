import IMO2020.N4.N4_basic extra.number_theory.totient_bound data.nat.prime_norm_num

/-! # IMO 2020 N4, Generalized Version (Part 1) -/

namespace IMOSL
namespace IMO2020N4

open finset function

def alternating (p a b : ℕ) :=
  {i : ℕ | (F p)^[i] a < (F p^[i]) b}.infinite ∧ {i : ℕ | (F p)^[i] b < (F p^[i]) a}.infinite

def good (p : ℕ) := ∃ a b : ℕ, a.coprime p ∧ b.coprime p ∧ alternating p a b



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

private lemma add_lt_mul {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) : a + b < a * b :=
begin
  have h : ∀ n : ℕ, 3 ≤ n → ∃ m : ℕ, n = m.succ :=
    λ n Y, nat.exists_eq_succ_of_ne_zero (ne_of_gt (lt_of_lt_of_le three_pos Y)),
  rcases h a ha with ⟨c, rfl⟩,
  rcases h b hb with ⟨d, rfl⟩,
  rw [nat.mul_succ, add_comm, nat.succ_mul, nat.succ_eq_one_add,
      add_lt_add_iff_right, add_lt_add_iff_right],
  rw [nat.succ_le_succ_iff, nat.succ_le_iff] at ha hb,
  exact nat.mul_lt_mul ha (le_of_lt hb) one_pos
end

private lemma two_pow_add_two_pow_ne_Mersenne {k : ℕ} (h : 3 ≤ k) :
  ∀ i j : ℕ, 2 ^ i + 2 ^ j ≠ 2 ^ k - 1 :=
begin
  suffices : ∀ i : ℕ, 2 ^ i + 1 + 1 ≠ 2 ^ k,
  { intros i j h0,
    rw eq_tsub_iff_add_eq_of_le (nat.one_le_two_pow k) at h0,
    rcases i.eq_zero_or_pos with rfl | hi,
    rw [pow_zero, add_comm 1] at h0; exact this j h0,
    rcases j.eq_zero_or_pos with rfl | hj,
    exact this i h0,
    replace h0 : even (2 ^ i + 2 ^ j + 1) ↔ even (2 ^ k) := by rw h0,
    revert h0; rw [imp_false, nat.even_add_one, ← not_iff, not_not, nat.even_add],
    replace this : ∀ c : ℕ, 0 < c → even (2 ^ c) :=
      λ c hc, (nat.even_pow' (ne_of_gt hc)).mpr even_two,
    replace h : 0 < k := lt_of_lt_of_le three_pos h,
    simp only [this, hi, hj, h, iff_self] },

  intros i h0,
  replace h0 : 2 ^ 3 ∣ 2 ^ i + 1 + 1 := by rw h0; exact pow_dvd_pow 2 h,
  clear h; revert h0; rw [add_assoc, imp_false],
  cases le_or_lt 3 i with h h,
  rw ← nat.dvd_add_iff_right (pow_dvd_pow 2 h),
  all_goals { apply nat.not_dvd_of_pos_of_lt; norm_num },
  rw nat.lt_succ_iff at h,
  refine lt_of_le_of_lt (add_le_add_right (pow_mono one_le_two h) _) _,
  norm_num
end

private lemma two_pow_or_sub_two_pow {k : ℕ} (h : k = 3 ∨ k = 4) :
  ∀ {x : ℕ}, x.coprime (2 ^ k - 1) → x < 2 ^ k - 1 →
    ∃ i : ℕ, i < k ∧ (x = 2 ^ i ∨ x = 2 ^ k - 1 - 2 ^ i) :=
begin
  ---- First reduce to a set equality
  suffices : (image (λ i, 2 ^ i) (range k) ∪ image (λ i, 2 ^ k - 1 - 2 ^ i) (range k)) =
    (filter (nat.coprime (2 ^ k - 1)) (range (2 ^ k - 1))),
  { intros x h0 h1,
    replace h1 : x ∈ filter (nat.coprime (2 ^ k - 1)) (range (2 ^ k - 1)) :=
      by rw [mem_filter, mem_range]; exact ⟨h1, h0.symm⟩,
    clear h0; rw [← this, mem_union, mem_image, mem_image] at h1,
    rcases h1 with ⟨i, h1, rfl⟩ | ⟨i, h1, rfl⟩; rw mem_range at h1,
    exacts [⟨i, h1, or.inl rfl⟩, ⟨i, h1, or.inr rfl⟩] },

  have h0 : 1 < k := by rcases h with rfl | rfl; norm_num,
  refine eq_of_subset_of_card_le (λ x h1, _) (le_of_eq _),
  
  ---- RHS contains LHS
  { rw [mem_filter, mem_range],
    simp only [mem_union, mem_image, mem_range] at h1,
    rcases h1 with ⟨i, h1, rfl⟩ | ⟨i, h1, rfl⟩; split,
    exact two_pow_lt_Mersenne h0 h1,
    exact (two_coprime_p (Mersenne_odd (pos_of_gt h0))).symm.pow_right i,
    rw [tsub_lt_self_iff, tsub_pos_iff_lt],
    exact ⟨nat.one_lt_two_pow k (pos_of_gt h0), pow_pos two_pos i⟩,
    replace h1 := two_pow_lt_Mersenne h0 h1,
    rw lt_iff_exists_add at h1,
    rcases h1 with ⟨c, h1, h2⟩,
    rw [h2, nat.add_sub_cancel_left, nat.coprime_add_self_left,
        ← nat.coprime_add_self_right, add_comm, ← h2],
    exact (two_coprime_p (Mersenne_odd (pos_of_gt h0))).pow_left i },

  ---- LHS and RHS has the same cardinality
  { have X : ∀ i j, 2 ^ i = 2 ^ j → i = j := nat.pow_right_injective (le_refl 2),
    rw [← nat.totient, card_union_eq, card_image_of_injective _ X,
        card_image_of_inj_on (λ i hi j hj h1, X i j _), card_range],

    -- The main equality: `φ(2^k - 1) = 2k` for `k = 3, 4`
    { rcases h with rfl | rfl; norm_num,
      rw nat.totient_prime (by norm_num : nat.prime 7),
      change 15 with 3 * 5,
      rw [nat.totient_mul, nat.totient_prime, nat.totient_prime],
      all_goals { norm_num } },

    -- If `2^k - 1 - 2^i = 2^k - 1 - 2^j`, then `i = j`
    { rw [mem_coe, mem_range] at hi hj,
      replace X : ∀ i : ℕ, i < k → 2 ^ i ≤ 2 ^ k - 1 :=
        λ i Y, le_of_lt (two_pow_lt_Mersenne h0 Y),
      exact (tsub_right_inj (X i hi) (X j hj)).mp h1 },

    -- `2^i ≠ 2^k - 1 - 2^j` for any `i, j < k`
    { rw [disjoint_iff, inf_eq_inter, bot_eq_empty, eq_empty_iff_forall_not_mem],
      intros c h1,
      simp only [inf_eq_inter, mem_image, mem_inter, le_eq_subset] at h1,
      rcases h1 with ⟨⟨i, -, rfl⟩, ⟨j, h1, h2⟩⟩,
      rw mem_range at h1,
      revert h2; rw nat.sub_eq_iff_eq_add (le_of_lt (two_pow_lt_Mersenne h0 h1)),
      refine (two_pow_add_two_pow_ne_Mersenne _ i j).symm,
      rcases h with rfl | rfl; norm_num } }
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

    -- Finishing
    replace h1 := F_switch_sign h0 h1,
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
      mul_left_injective₀ (ne_of_gt (order_two_mod_p_pos h)),
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
  replace h0 := extra.exists_nontrivial_coprime h h0,
  rcases h0 with ⟨c, d, h0, h1, h2, rfl⟩,
  replace h : nat.coprime (2 ^ c - 1) (2 ^ (c + d) - 1) :=
    by unfold nat.coprime at h2 ⊢; rw [pow_sub_one_gcd, nat.gcd_self_add_right, h2, pow_one],
  refine ⟨2 ^ c - 1, 2 ^ d * (2 ^ c - 1), h, ((two_coprime_p X).pow_left _).mul h, _⟩,
  rw and_comm; refine ⟨⟨_, by rw S0_two_pow_mul⟩, _⟩,
  rw [nat.mul_sub_left_distrib, mul_one, ← pow_add, add_comm],
  exact tsub_lt_tsub_left_of_le (nat.pow_le_pow_of_le_right two_pos le_add_self)
    (nat.one_lt_two_pow d (lt_trans one_pos h1)),
  
  ---- Now focus on the main inequality.
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
  rw [nat.succ_sub_one, nat.succ_mul, nat.mul_succ, nat.succ_mul, add_lt_add_iff_right,
      nat.succ_eq_add_one, ← add_assoc, nat.add_sub_cancel, nat.div_lt_iff_lt_mul two_pos,
      mul_comm, mul_two, add_assoc, add_lt_add_iff_left, mul_comm],
  exact add_lt_mul h0 h1
end

private lemma Mersenne_small_bad {k : ℕ} (h : 0 < k) (h0 : k < 5) : ¬good (2 ^ k - 1) :=
begin
  have X : odd (2 ^ k - 1) := Mersenne_odd h,
  rw [nat.lt_succ_iff, le_iff_lt_or_eq, nat.lt_succ_iff, le_iff_lt_or_eq, or_assoc] at h0,
  rw good_iff' X; rcases h0 with h0 | h0,

  ---- Easy case: `k ≤ 2`
  { rw [nat.lt_succ_iff, le_iff_lt_or_eq, nat.lt_succ_iff, le_iff_lt_or_eq, nat.lt_one_iff] at h0,
    rintros ⟨x, y, h1, -, h2, h3, -⟩; clear X,
    rcases h0 with (rfl | rfl) | rfl,
    exact lt_irrefl 0 h,
    rw [pow_one, bit0, nat.add_sub_cancel, nat.lt_one_iff] at h3,
    exact ne_of_gt (pos_of_gt h2) h3,
    norm_num at h1 h2 h3,
    rw [← nat.add_one_le_iff, le_iff_exists_add] at h2,
    rcases h2 with ⟨c, rfl⟩,
    rw [add_right_comm, nat.succ_lt_succ_iff, add_assoc, add_comm,
        nat.succ_lt_succ_iff, nat.lt_one_iff, add_eq_zero_iff] at h3,
    rcases h3 with ⟨rfl, -⟩,
    rw nat.coprime_zero_left at h1,
    revert h1; norm_num },

  ---- Hard case: `k = 3` and `k = 4`
  {  -- Setup
    set n := 2 ^ k - 1,
    have Y : ∀ x : ℕ, x.coprime n → x < n → ∃ i : ℕ, i < k ∧ (x = 2 ^ i ∨ x = n - 2 ^ i) :=
      λ x, two_pow_or_sub_two_pow h0,
    rintros ⟨x, y, h1, h2, h3, h4, h5⟩,
    replace h1 := Y x h1 (lt_trans (lt_of_le_of_lt le_add_self h3) h4),
    replace h2 := Y y h2 h4,
    revert h3 h5; rw [imp_false, imp_iff_not_or, not_lt],
    replace h : 2 < k := by rcases h0 with rfl | rfl; norm_num,
    replace h4 : n ≠ (k - 1) * n := ne_of_lt (lt_mul_left X.pos (lt_tsub_iff_left.mpr h)),
    replace h0 : 1 < k := lt_trans one_lt_two h,
    replace Y : ∀ i j : ℕ, i < k → 2 ^ i ≤ n / 2 + 2 ^ j :=
    begin
      intros i j hi,
      refine le_trans _ (add_le_add_left j.one_le_two_pow _),
      rw [← nat.add_mul_div_right _ _ two_pos, one_mul,
          nat.le_div_iff_mul_le two_pos, ← pow_succ'],
      rw ← nat.succ_le_iff at hi; refine le_trans (pow_mono one_le_two hi) _,
      change 2 ^ k ≤ 2 ^ k - 1 + 1 + 1,
      rw nat.sub_add_cancel k.one_le_two_pow; exact le_self_add
    end,

    -- Case divisions
    rcases h1 with ⟨i, h1, rfl | rfl⟩; rcases h2 with ⟨j, h2, rfl | rfl⟩,
    left; exact Y j i h2,
    right; rw [S0_two_pow, S0_Mersenne_one X h0, S0_Mersenne_neg_two_pow X h0 h2]; exact h4,
    right; rw [S0_two_pow, S0_Mersenne_one X h0, S0_Mersenne_neg_two_pow X h0 h1]; exact h4.symm,
    left; replace Y := Y i j h1,
    rw [tsub_le_iff_right, add_right_comm, ← nat.add_sub_assoc,
        le_tsub_iff_left (le_trans Y le_self_add), add_le_add_iff_right],
    exacts [Y, le_of_lt (two_pow_lt_Mersenne h0 h1)] }
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
