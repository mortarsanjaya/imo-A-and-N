import data.int.modeq ring_theory.coprime.lemmas

/-! # IMO 2007 N6 (P5) -/

namespace IMOSL
namespace IMO2007N6

def bad (n a b : ℤ) := n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2

variables {n : ℤ} (hn : 1 < n)
include hn

private lemma lem1 (a b : ℤ) : bad n a b ↔ n * a * b - 1 ∣ (a - b) ^ 2 :=
begin
  have h : n * a ^ 2 - n * a * b ≡ n * a ^ 2 - 1 [ZMOD n * a * b - 1] :=
    by rw [int.modeq_iff_dvd, sub_sub_sub_cancel_left],
  replace h := int.modeq.pow 2 h,
  rw int.modeq at h,
  rw [bad, int.dvd_iff_mod_eq_zero, ← h, ← int.dvd_iff_mod_eq_zero,
      sq a, ← mul_assoc, ← mul_sub, mul_pow],
  refine ⟨is_coprime.dvd_of_dvd_mul_left (is_coprime.pow_right ⟨-1, b, _⟩),
          λ h0, dvd_mul_of_dvd_right h0 _⟩,
  rw [neg_one_mul, neg_sub, mul_comm, sub_add_cancel]
end

private lemma lem2 {a b : ℤ} (h : bad n a b) : bad n b a :=
begin
  rw lem1 hn at h ⊢,
  convert h using 1,
  rw mul_right_comm,
  rw [sub_sq, sub_sq, sub_add_comm, mul_right_comm]
end

private lemma lem3 {a b : ℤ} (h : bad n a b) (h0 : 0 < a) (h1 : a < b) :
  ∃ c : ℤ, bad n c a ∧ 0 < c ∧ c < a :=
begin
  cases h with k h,
  obtain ⟨c, rfl⟩ : ∃ c : ℤ, k = n * a * c - 1 :=
  begin
    replace h := congr_arg (λ x, x % (n * a)) h; simp only [] at h,
    rw [sub_one_mul, mul_assoc, sq a, sub_sq, ← mul_assoc, one_pow, mul_one] at h,
    generalize hx : n * a = x,
    rw [hx, sq, ← sub_mul, mul_comm x, ← mul_assoc, add_comm, int.add_mul_mod_self,
        sub_eq_add_neg, add_comm, int.add_mul_mod_self_left, eq_comm, ← int.modeq,
        int.modeq_iff_dvd, sub_neg_eq_add, add_comm] at h,
    cases h with c h,
    use c; rw [eq_sub_iff_add_eq, h]
  end,
  refine ⟨c, lem2 hn ⟨n * a * b - 1, by rw [h, mul_comm]⟩, _⟩,
  have h2 : ∀ x y : ℤ, x < y ↔ n * a * x - 1 < n * a * y - 1 :=
    λ x y, by rw [sub_lt_sub_iff_right, ← mul_lt_mul_left (mul_pos (lt_trans one_pos hn) h0)],
  rw [h2, mul_zero, int.sub_one_lt_iff] at h0 ⊢,
  rw h2 at h1 ⊢; split,
  exact (zero_le_mul_left (lt_of_le_of_lt h0 h1)).mp (le_of_le_of_eq (sq_nonneg _) h),
  rw ← not_le; intros h3,
  revert h; rw [sq a, ← mul_assoc, sq],
  rw le_iff_lt_or_eq at h0,
  cases h0 with h0 h0,
  refine ne_of_lt (int.mul_lt_mul h1 h3 h0 (le_of_lt (lt_trans h0 h1))),
  exfalso; revert hn,
  refine not_lt_of_le (int.le_of_dvd one_pos _),
  use (a * a); rwa [← mul_assoc, eq_comm, ← sub_eq_zero, eq_comm]
end



/-- Final solution -/
theorem final_solution {a b : ℤ} (h : bad n a b) (h0 : 0 < a) (h1 : 0 < b) : a = b :=
begin
  wlog h2 : a ≤ b,
  work_on_goal 2 { exact (this (lem2 hn h) h1 h0).symm },
  rw le_iff_eq_or_lt at h2,
  cases h2 with h2 h2,
  exact h2,
  exfalso; clear h1,
  lift b to ℕ using le_of_lt (lt_trans h0 h2),
  induction b using nat.strong_induction_on with b b_ih generalizing h h0 h2 a,
  lift a to ℕ using le_of_lt h0,
  rcases lem3 hn h h0 h2 with ⟨c, h1, h3, h4⟩,
  exact b_ih a (nat.cast_lt.mp h2) h3 h1 h4
end

end IMO2007N6
end IMOSL
