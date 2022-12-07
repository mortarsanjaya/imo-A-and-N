import algebra.big_operators.basic data.nat.digits

/-! # IMO 2010 A4 -/

namespace IMOSL
namespace IMO2010A4

open finset

def x : ℕ → bool := nat.binary_rec ff (λ odd k, bxor (bor odd k.bodd))
def S (n : ℕ) : ℤ := (range n).sum (λ k, cond (x k) (-1) 1)



section x_prop

private lemma x_zero : x 0 = ff := by rw [x, nat.binary_rec_zero]

private lemma x_mul2 (k : ℕ) : x (2 * k) = bxor k.bodd (x k) :=
begin
  rw [x, ← nat.bit0_val],
  refine nat.binary_rec_eq _ ff k,
  rw [ff_bor, bxor_ff, nat.bodd_zero]
end

private lemma x_mul2_add1 (k : ℕ) : x (2 * k + 1) = !(x k) :=
begin
  rw [x, ← nat.bit1_val, ← tt_bxor],
  refine nat.binary_rec_eq _ tt k,
  rw [ff_bor, bxor_ff, nat.bodd_zero]
end

private lemma x_mul4_lem1 (k : ℕ) : x (4 * k + 1) = !(x (4 * k)) :=
  by rw [bit0, ← two_mul, mul_assoc, x_mul2, x_mul2_add1, ← nat.bit0_val, nat.bodd_bit0, ff_bxor]

private lemma x_mul4_lem2 (k : ℕ) : x (4 * k + 2) = x k :=
  by rw [bit0, ← two_mul, mul_assoc, ← mul_add_one, x_mul2,
    x_mul2_add1, ← nat.bit1_val, nat.bodd_bit1, tt_bxor, bnot_bnot]

private lemma x_mul4_lem3 (k : ℕ) : x (4 * k + 3) = x k :=
  by rw [bit0, ← two_mul, bit1, ← add_assoc, mul_assoc,
    ← mul_add_one, x_mul2_add1, x_mul2_add1, bnot_bnot]

end x_prop



section S_prop

private lemma S_zero : S 0 = 0 :=
  by rw [S, sum_range_zero]

private lemma S_succ (a : ℕ) : S a.succ = S a + cond (x a) (-1) 1 :=
  by rw [S, sum_range_succ, ← S]

private lemma S_mul4_add2 (k : ℕ) : S (4 * k + 2) = S (4 * k) :=
begin
  rw [S_succ, S_succ, add_assoc, add_right_eq_self, x_mul4_lem1],
  generalize : x (4 * k) = b,
  cases b; refl
end

private lemma S_mul4 (k : ℕ) : S (4 * k) = 2 * S k :=
begin
  induction k with k k_ih,
  rw [mul_zero, S_zero, mul_zero],
  rw [nat.mul_succ, bit0, S_succ, x_mul4_lem3, S_succ, x_mul4_lem2,
      S_mul4_add2, k_ih, add_assoc, ← two_mul, ← mul_add, ← S_succ]
end

private lemma S_parity (k : ℕ) : (S k).bodd = k.bodd :=
begin
  induction k with k k_ih,
  rw S_zero; refl,
  rw [nat.bodd_succ, S_succ, int.bodd_add, k_ih, ← bxor_tt],
  congr'; generalize : x k = b,
  cases b; refl
end

private lemma S_four_mul_add_eq_zero_iff (q : ℕ) {r : ℕ} (h : r < 4) :
  S (4 * q + r) = 0 ↔ S q = 0 ∧ (r = 0 ∨ r = 2) :=
begin
  ---- If `S_q = 0` and `r ∈ {0, 2}`, then `S_{4q + r} = 0`
  symmetry; refine ⟨λ h0, _, λ h0, _⟩,
  rcases h0 with ⟨h0, rfl | rfl⟩,
  rw [add_zero, S_mul4, h0, mul_zero],
  rw [S_mul4_add2, S_mul4, h0, mul_zero],

  ---- If `S_{4q + r} = 0` and `r ∈ {0, 2}`, then `S_q = 0`
  refine (and_iff_right_of_imp _).mpr _,
  replace h : (2 : ℤ) ≠ 0 := two_ne_zero,
  rintros (rfl | rfl),
  rwa [add_zero, S_mul4, mul_eq_zero, or_iff_right h] at h0,
  rwa [S_mul4_add2, S_mul4, mul_eq_zero, or_iff_right h] at h0,

  ---- If `S_{4q + r} = 0`, then `r ∈ {0, 2}`
  apply_fun int.bodd at h0,
  rw [int.bodd_zero, S_parity, nat.bodd_add, nat.bodd_mul, nat.bodd_bit0, ff_band, ff_bxor] at h0,
  simp_rw [nat.lt_succ_iff_lt_or_eq, not_lt_zero', false_or, or_assoc] at h,
  rw [or_comm, or_rotate, or_comm, ← or_assoc] at h,
  revert h; refine (or_iff_left _).mp,
  rintros (rfl | rfl); revert h0; norm_num
end

end S_prop







/-- Final solution -/
theorem final_solution : ∀ k : ℕ, 0 ≤ S k :=
begin
  ---- Reduce to showing that `x_k = ff` whenever `S_k = 0`
  suffices : ∀ k : ℕ, S k = 0 → x k = ff,
  { intros k; induction k with k k_ih,
    rw S_zero,
    rw [le_iff_lt_or_eq, int.lt_iff_add_one_le, zero_add, or_comm] at k_ih,
    rw S_succ; cases k_ih with h h,
    rw [← h, zero_add, this k h.symm, bool.cond_ff]; exact zero_le_one,
    rw ← add_neg_self (1 : ℤ); refine add_le_add h _,
    generalize : x k = b,
    clear this h k; cases b,
    rw [bool.cond_ff, neg_le_self_iff]; exact zero_le_one,
    rw bool.cond_tt },
  
  ---- Now show that `x_k = ff` whenever `S_k = 0`, using strong induction
  intros k h; induction k using nat.strong_induction_on with k k_ih,
  obtain ⟨q, r, h0, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ 4 * q + r = k :=
    ⟨k / 4, k % 4, nat.mod_lt k four_pos, nat.div_add_mod k 4⟩,
  rw [S_four_mul_add_eq_zero_iff q h0, or_comm] at h,
  clear h0; rcases h with ⟨h, rfl | rfl⟩,
  rw x_mul4_lem2; exact k_ih q (lt_add_of_le_of_pos (nat.le_mul_of_pos_left four_pos) two_pos) h,
  rcases q.eq_zero_or_pos with rfl | h0,
  rw [add_zero, mul_zero, x_zero],
  replace k_ih := k_ih q (lt_mul_left h0 (by norm_num : 1 < 4)) h,
  apply_fun int.bodd at h; rw [int.bodd_zero, S_parity] at h,
  rw [add_zero, bit0, ← two_mul, mul_assoc, x_mul2, nat.bodd_mul,
      nat.bodd_bit0, ff_band, ff_bxor, x_mul2, h, k_ih, ff_bxor]
end



/-- Extra part -/
theorem final_solution_extra (k : ℕ) :
  S k = 0 ↔ ∀ c : ℕ, c ∈ nat.digits 4 k → c = 0 ∨ c = 2 :=
begin
  induction k using nat.strong_induction_on with k k_ih,
  obtain ⟨q, r, h, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ 4 * q + r = k :=
    ⟨k / 4, k % 4, nat.mod_lt k four_pos, nat.div_add_mod k 4⟩,
  rw S_four_mul_add_eq_zero_iff q h,
  rcases q.eq_zero_or_pos with rfl | h0,

  ---- Case 1: `q = 0`
  rw [S_zero, eq_self_iff_true, true_and, mul_zero, zero_add],
  rcases r.eq_zero_or_pos with rfl | h0,
  rw [eq_self_iff_true, true_or, true_iff, nat.digits_zero],
  intros c h0; exfalso; exact h0,
  rw [nat.digits_def' (le_add_self : 2 ≤ 2 + 2) h0,
      nat.mod_eq_of_lt h, nat.div_eq_zero h, nat.digits_zero],
  simp_rw [list.mem_singleton, forall_eq],

  ---- Case 2: `0 < q`
  replace k_ih := k_ih q (nat.lt_add_right q (4 * q) r (lt_mul_left h0 (by norm_num : 1 < 4))),
  rw [k_ih, add_comm, nat.digits_add 4 le_add_self r q h (or.inr h0)]; clear k_ih h h0,
  simp_rw [list.mem_cons_iff, forall_eq_or_imp, and_comm]
end

end IMO2010A4
end IMOSL
