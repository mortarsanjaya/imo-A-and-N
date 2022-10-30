import IMO2020.N4.N4_basic extra.number_theory.totient_bound

/-! # IMO 2020 N4, Generalized Version (Part 1) -/

namespace IMOSL
namespace IMO2020N4

open function

def alternating (p a b : ℕ) :=
  {i : ℕ | (F p)^[i] a < (F p^[i]) b}.infinite ∧ {i : ℕ | (F p)^[i] b < (F p^[i]) a}.infinite

def good (p : ℕ) := ∃ a b : ℕ, a.coprime p ∧ b.coprime p ∧ alternating p a b



section results

variables {p : ℕ} (h : odd p)
include h

private lemma lem1 : ∀ {a b : ℕ}, alternating p a b → S0 h a = S0 h b :=
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
  obtain ⟨N, h2⟩ := main_lemma h h0,
  obtain ⟨n, h3, h4⟩ := h1.exists_nat_lt N,
  exact lt_asymm (set.mem_set_of_eq.mp h3) (h2 n (le_of_lt h4))
end

private lemma lem2 {a b : ℕ} (h0 : alternating p a b) :
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

private lemma lem3 {a b : ℕ} (h0 : b < a) (h1 : F p a < F p b) :
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

private lemma lem4 : good p ↔
  (∃ x y : ℕ, x.coprime p ∧ y.coprime p ∧ p / 2 + x < y ∧ y < p ∧ S0 h x = S0 h y) :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,
  { rcases h0 with ⟨a, b, ha, hb, h0⟩,
    have h1 := lem1 h h0,
    obtain ⟨N, h2, h3⟩ := lem2 h h0,
    rw [iterate_succ', comp_app, comp_app] at h3,
    replace ha := F_iterate_coprime h ha N,
    replace hb := F_iterate_coprime h hb N,
    rw [← S0_F_iterate h N, ← S0_F_iterate h N b] at h1,
    generalize_hyp : (F p^[N]) a = c at ha h1 h2 h3,
    generalize_hyp : (F p^[N]) b = d at hb h1 h2 h3,
    obtain ⟨k, x, y, h4, h5, rfl, rfl⟩ := lem3 h h2 h3,
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



private lemma lem5 (h0 : ∀ k : ℕ, p + 1 ≠ 2 ^ k) : good p :=
begin
  rw lem4 h,
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
  refine ⟨1, 2 ^ c, p.coprime_one_left, (two_coprime_p h).pow_left c, _, h2, _⟩,
  work_on_goal 2 { rw [← mul_one (2 ^ c), S0_two_pow_mul] },
  rw [← nat.add_mul_div_right _ _ two_pos, nat.div_lt_iff_lt_mul two_pos, ← pow_succ', one_mul],
  replace h2 : even (2 ^ c.succ) := nat.even_pow.mpr ⟨even_two, c.succ_ne_zero⟩,
  rw nat.odd_iff_not_even at h,
  rw [le_iff_eq_or_lt, ← nat.add_one_le_iff, le_iff_eq_or_lt, ← nat.add_one_le_iff] at h1,
  rcases h1 with rfl | h1 | h1,
  exfalso; exact h h2,
  exfalso; exact h0 c.succ h1,
  rw le_iff_lt_or_eq at h1; cases h1 with h1 h1,
  exact h1,
  rw [← h1, add_assoc, nat.even_add, iff_true_intro even_two, iff_true] at h2,
  exfalso; exact h h2
end

private lemma lem6 {k : ℕ} (h0 : p + 1 = 2 ^ k) (h1 : 5 ≤ k) : good p :=
begin
  rw lem4 h,
  sorry
end

private lemma lem7 {k : ℕ} (h0 : k ∈ ({1, 3, 7, 15} : finset ℕ)) : ¬good p :=
begin
  rw lem4 h,
  sorry
end

end results





/-- Final solution -/
theorem final_solution_part1' {p : ℕ} (h : odd p) :
  good p ↔ p ∉ ({1, 3, 7, 15} : finset ℕ) :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,
  contrapose! h0; exact lem7 h h0,
  by_cases h1 : ∀ k : ℕ, p + 1 ≠ 2 ^ k,
  exact lem5 h h1,
  simp only [not_forall, not_not] at h1,
  cases h1 with k h1,
  refine lem6 h h1 (le_of_not_lt _),
  contrapose! h0; simp only [finset.mem_insert, finset.mem_singleton],
  repeat { rw [nat.lt_succ_iff, le_iff_lt_or_eq] at h0 },
  repeat { rw [or_assoc] at h0 },
  rcases h0 with h0 | rfl | h0,
  exfalso; exact not_le_of_lt h0 k.zero_le,
  rw [pow_zero, add_left_eq_self] at h1,
  rw [h1, nat.odd_iff_not_even] at h,
  exfalso; exact h even_zero,
  rw [eq_comm, ← nat.sub_eq_iff_eq_add (nat.one_le_pow k 2 two_pos)] at h1; subst h1,
  rcases h0 with rfl | rfl | rfl | rfl; norm_num
end

end IMO2020N4
end IMOSL