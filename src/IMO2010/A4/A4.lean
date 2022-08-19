import data.finset.basic algebra.big_operators.basic data.nat.digits

/-! # IMO 2010 A4 -/

namespace IMOSL
namespace IMO2010A4

open finset



def x : ℕ → bool := nat.binary_rec ff (λ odd k, bxor (bor odd k.bodd))
def bool_int (b : bool) : ℤ := cond b (-1) 1
def S (n : ℕ) : ℤ := (range n).sum (bool_int ∘ x)

private lemma bool_int_bnot (b : bool) : bool_int (!b) = - bool_int b :=
  by cases b; refl

private lemma bool_int_bodd (b : bool) : (bool_int b).bodd = tt :=
  by cases b; refl

private lemma bool_int_ge_neg_one (b : bool) : -1 ≤ bool_int b :=
  by cases b; simp [bool_int]

private lemma bool_int_nonneg_iff (b : bool) : 0 ≤ bool_int b ↔ b = ff :=
  by cases b; simp [bool_int]



private lemma x_zero : x 0 = ff :=
  by simp only [x, nat.binary_rec_zero]

private lemma x_mul2 (k : ℕ) : x (2 * k) = bxor k.bodd (x k) :=
begin
  rw [x, ← nat.bit0_val],
  change bit0 k with nat.bit ff k,
  rw [nat.binary_rec_eq, ff_bor],
  rw [ff_bor, bxor_ff, nat.bodd_zero]
end

private lemma x_mul2_add1 (k : ℕ) : x (2 * k + 1) = !(x k) :=
begin
  rw [x, ← nat.bit1_val],
  change bit1 k with nat.bit tt k,
  rw [nat.binary_rec_eq, tt_bor, tt_bxor],
  rw [ff_bor, bxor_ff, nat.bodd_zero]
end

private lemma x_mul4_lem1 (k : ℕ) : x (4 * k + 1) = !(x (4 * k)) :=
  by rw [bit0, ← two_mul, mul_assoc, x_mul2, x_mul2_add1,
         ← nat.bit0_val, nat.bodd_bit0, ff_bxor]

private lemma x_mul4_lem2 (k : ℕ) : x (4 * k + 2) = x k :=
  by rw [bit0, ← two_mul, mul_assoc, ← mul_add_one, x_mul2, x_mul2_add1,
        ← nat.bit1_val, nat.bodd_bit1, tt_bxor, bnot_bnot]

private lemma x_mul4_lem3 (k : ℕ) : x (4 * k + 3) = x k :=
  by rw [bit0, ← two_mul, bit1, ← add_assoc, mul_assoc,
         ← mul_add_one, x_mul2_add1, x_mul2_add1, bnot_bnot]



private lemma S_zero : S 0 = 0 :=
  by rw [S, sum_range_zero]

private lemma S_add (a b : ℕ) : S (a + b) = S a + (range b).sum (λ k, bool_int (x (a + k))) :=
  by dsimp only [S]; rw sum_range_add

private lemma S_succ (a : ℕ) : S a.succ = S a + bool_int (x a) :=
  by dsimp only [S]; rw sum_range_succ

private lemma S_mul4_add2 (k : ℕ) : S (4 * k + 2) = S (4 * k) :=
  by rw [S_add, sum_range_succ, sum_range_one, x_mul4_lem1,
         add_zero, bool_int_bnot, add_neg_self, add_zero]

private lemma S_mul4 (k : ℕ) : S (4 * k) = 2 * S k :=
begin
  induction k with k k_ih,
  rw [mul_zero, S_zero, mul_zero],
  rw [nat.mul_succ, bit0, ← add_assoc, S_add, S_mul4_add2, k_ih, S_succ, mul_add, add_right_inj,
      sum_range_succ, sum_range_one, add_zero, x_mul4_lem2, add_assoc, x_mul4_lem3, ← two_mul]
end

private lemma S_parity (k : ℕ) : (S k).bodd = k.bodd :=
begin
  induction k with k k_ih,
  rw S_zero; refl,
  rw [S_succ, nat.bodd_succ, int.bodd_add, k_ih, bool_int_bodd, bxor_tt]
end

private lemma S_zeroes_even {k : ℕ} (h : S k = 0) : k % 2 = 0 :=
  by rw [nat.mod_two_of_bodd, ← S_parity, h, int.bodd_zero, bool.cond_ff]

private lemma S_zeroes_iff (k : ℕ) : S k = 0 ↔ (k % 4 = 0 ∨ k % 4 = 2) ∧ (S (k / 4) = 0) :=
begin
  nth_rewrite 0 ← nat.div_add_mod k 4,
  generalizes [h : k / 4 = q, h0 : k % 4 = r],
  have h1 : r < 4 := by rw h0; exact nat.mod_lt k four_pos,
  clear h h0 k; split,
  { intros h,
    refine (and_iff_left_of_imp _).mpr _,
    rintros (rfl | rfl),
    rwa [add_zero, S_mul4, mul_eq_zero, or_iff_right (two_ne_zero : (2 : ℤ) ≠ 0)] at h,
    rwa [S_mul4_add2, S_mul4, mul_eq_zero, or_iff_right (two_ne_zero : (2 : ℤ) ≠ 0)] at h,
    replace h := S_zeroes_even h,
    rw [bit0, ← two_mul, mul_assoc, mul_comm, nat.mul_add_mod, ← nat.dvd_iff_mod_eq_zero] at h,
    rcases h with ⟨c, rfl⟩,
    change 4 with 2 + 2 at h1,
    rw [← two_mul, mul_lt_mul_left (two_pos : 0 < 2), nat.lt_succ_iff,
        nat.le_add_one_iff, zero_add, nonpos_iff_eq_zero] at h1,
    rcases h1 with rfl | rfl,
    left; rw mul_zero,
    right; rw mul_one },
  { rintros ⟨(rfl | rfl), h⟩,
    rw [add_zero, S_mul4, h, mul_zero],
    rw [S_mul4_add2, S_mul4, h, mul_zero] }
end

private lemma S_zeroes_x_eq_ff {k : ℕ} (h : S k = 0) : x k = ff :=
begin
  induction k using nat.strong_induction_on with k k_ih,
  cases k.eq_zero_or_pos with h0 h0,
  rw [h0, x_zero],
  rw S_zeroes_iff at h; cases h with h h1,
  replace k_ih := k_ih (k / 4) (nat.div_lt_self h0 (by norm_num)) h1,
  generalizes [h2 : k / 4 = q, h3 : k % 4 = r],
  rw [← nat.div_add_mod k 4, ← h2, ← h3],
  rw ← h2 at h1 k_ih; rw ← h3 at h; clear h2 h3 h0 k,
  rw or_comm at h; rcases h with rfl | rfl,
  rwa x_mul4_lem2,
  replace h1 := S_zeroes_even h1,
  rw ← nat.dvd_iff_mod_eq_zero at h1; rcases h1 with ⟨q, rfl⟩,
  rw [add_zero, bit0, ← mul_two, mul_assoc],
  repeat { rw [x_mul2, nat.bodd_mul, nat.bodd_bit0, ff_band, ff_bxor, x_mul2, k_ih] },
  rw [bxor_ff, nat.bodd_mul, nat.bodd_bit0, ff_band]
end



/-- Final solution -/
theorem final_solution (k : ℕ) : 0 ≤ S k :=
begin
  induction k with k k_ih,
  rw S_zero,
  rw [le_iff_lt_or_eq, int.lt_iff_add_one_le, zero_add, eq_comm] at k_ih,
  rw S_succ; cases k_ih with h h,
  rw ← add_neg_self (1 : ℤ); exact add_le_add h (bool_int_ge_neg_one _),
  rw [h, zero_add, bool_int_nonneg_iff]; exact S_zeroes_x_eq_ff h
end

/-- Extra part -/
theorem final_solution_extra (k : ℕ) :
  S k = 0 ↔ ∀ c : ℕ, c ∈ nat.digits 4 k → c = 0 ∨ c = 2 :=
begin
  induction k using nat.strong_induction_on with k k_ih,
  cases k.eq_zero_or_pos with h h,
  { rw [h, S_zero, eq_self_iff_true, true_iff, nat.digits_zero],
    intros c h0; exfalso; exact list.not_mem_nil c h0 },
  { replace k_ih := k_ih (k / 4) (nat.div_lt_self h (by norm_num)),
    rw [S_zeroes_iff, k_ih, nat.digits_def' (by norm_num : 2 ≤ 4) h],
    simp only [list.mem_cons_iff, forall_eq_or_imp] }
end

end IMO2010A4
end IMOSL
