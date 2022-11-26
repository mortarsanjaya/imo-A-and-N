import data.int.modeq tactic.wlog

/-! # IMO 2007 N6 (P5) -/

namespace IMOSL
namespace IMO2007N6

private lemma bad_symm {n : ℤ} {a b : ℕ} (h : n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2) :
  n * b * a - 1 ∣ (n * b ^ 2 - 1) ^ 2 :=
begin
  rw [mul_right_comm, sub_sq', add_comm, mul_right_comm _ _ (1 : ℤ), ← sub_sq'],
  replace h := dvd_mul_of_dvd_left h ((n * b ^ 2) ^ 2),
  rw [← mul_pow, sub_one_mul, mul_mul_mul_comm, ← sq, ← mul_pow, ← mul_pow, ← mul_assoc] at h,
  rw ← int.modeq_zero_iff_dvd at h ⊢,
  revert h; refine ((int.modeq.sub_right _ _).pow _).trans,
  nth_rewrite 1 ← one_pow 2,
  exact ((n * a * b).modeq_sub 1).symm.pow 2
end

private lemma bad_exists_descent {n : ℤ} (hn : 1 < n) {a : ℕ}
  (h : 0 < a ∧ ∃ b : ℕ, a < b ∧ n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2) :
  ∃ c : ℕ, 0 < c ∧ c < a ∧ n * c * a - 1 ∣ (n * c ^ 2 - 1) ^ 2 :=
begin
  rcases h with ⟨h, b, h0, k, h1⟩,
  rw [sq (a : ℤ), ← mul_assoc] at h1,
  generalize_hyp ht : n * a = t at h1,
  obtain ⟨c, rfl⟩ : ∃ c : ℤ, k = t * c - 1 :=
  begin
    replace h1 : (t * a - 1) ^ 2 ≡ (t * b - 1) * k [ZMOD t] := by rw h1,
    have X : ∀ m : ℤ, t * m - 1 ≡ -1 [ZMOD t] :=
      λ m, by symmetry; rw [int.modeq_iff_dvd, sub_neg_eq_add, sub_add_cancel]; exact ⟨m, rfl⟩,
    replace h1 := ((X a).pow 2).symm.trans (h1.trans ((X b).mul_right _)),
    rw [int.modeq_iff_dvd, sq, ← mul_sub, sub_neg_eq_add, neg_one_mul, dvd_neg] at h1,
    cases h1 with c h1,
    use c; rw [eq_sub_iff_add_eq, h1]
  end,

  ---- It suffices to show that `0 < c` and `c < (a : ℤ)`
  suffices h2 : c < a ∧ 0 < c,
  { lift c to ℕ using le_of_lt h2.2,
    rw [int.coe_nat_pos, int.coe_nat_lt] at h2,
    refine ⟨c, h2.2, h2.1, bad_symm _⟩,
    use t * b - 1; rw [sq (a : ℤ), ← mul_assoc, ht, h1, mul_comm] },
  
  ---- We do not need `n`; we just use `t` instead.
  replace ht : 1 < t :=
  begin
    rw ← int.coe_nat_pos at h,
    have h2 := le_trans int.one_nonneg (le_of_lt hn),
    rw int.lt_iff_add_one_le at hn h ⊢,
    rw ← ht; refine le_of_eq_of_le _ (mul_le_mul hn h zero_le_one h2),
    rw [zero_add, mul_one]
  end,
  clear hn n,

  ---- Some ordering results
  have h2 := lt_trans one_pos ht,
  have h3 : ∀ x y : ℤ, x < y ↔ t * x - 1 < t * y - 1 :=
    λ x y, by rw [sub_lt_sub_iff_right, ← mul_lt_mul_left h2],
  replace h2 : ∀ x : ℤ, 0 < x ↔ 0 < t * x - 1 :=
  begin
    intros x,
    rw [h3, mul_zero, int.lt_iff_add_one_le, sub_add_cancel, le_iff_eq_or_lt],
    refine or_iff_right (λ h4, _),
    rw [eq_comm, sub_eq_zero] at h4,
    exact ne_of_gt ht (int.eq_one_of_mul_eq_one_right (le_of_lt h2) h4)
  end,

  ---- Rearranging and final step
  rw [← int.coe_nat_pos, h2] at h,
  rw [← int.coe_nat_lt, h3] at h0,
  rw [h2, h3 c],
  generalize_hyp : t * a - 1 = x at h h0 h1 ⊢,
  generalize_hyp : t * b - 1 = y at h0 h1 ⊢,
  generalize_hyp : t * c - 1 = z at h1 ⊢,
  clear ht h2 h3 a b c t; split,
  rwa [← mul_lt_mul_left (lt_trans h h0), ← h1, sq, mul_lt_mul_right h],
  rw [← mul_lt_mul_left (lt_trans h h0), mul_zero, ← h1],
  exact pow_pos h 2
end

private lemma nat_pred_descent {P : ℕ → Prop} [decidable_pred P]
    (h : ∀ k : ℕ, P k → ∃ m : ℕ, m < k ∧ P m) :
  ∀ k : ℕ, ¬P k :=
begin
  by_contra' h0,
  replace h := h (nat.find h0) (nat.find_spec h0),
  rcases h with ⟨m, h, h1⟩,
  exact nat.find_min h0 h h1
end







open_locale classical

/-- Final solution -/
theorem final_solution {n : ℤ} (hn : 1 < n) :
  ∀ a b : ℕ, 0 < a → 0 < b → n * a * b - 1 ∣ (n * a ^ 2 - 1) ^ 2 → a = b :=
begin
  let P : ℕ → Prop := λ k, (0 < k ∧ ∃ m : ℕ, k < m ∧ n * k * m - 1 ∣ (n * k ^ 2 - 1) ^ 2),
  have h : ∀ k : ℕ, P k → ∃ m : ℕ, m < k ∧ P m :=
  begin
    intros k h,
    replace h := bad_exists_descent hn h,
    rcases h with ⟨c, h, h0, h1⟩,
    exact ⟨c, h0, h, k, h0, h1⟩
  end,

  replace h := nat_pred_descent h,
  dsimp only [P] at h,
  intros a b ha hb h0; by_contra' h1,
  rw [← ne.def, ne_iff_lt_or_gt, gt_iff_lt] at h1,
  have h2 := bad_symm h0,
  wlog h1 : a < b := h1 using [a b, b a],
  exact h a ⟨ha, b, h1, h0⟩
end

end IMO2007N6
end IMOSL
