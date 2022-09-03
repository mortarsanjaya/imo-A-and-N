import data.pnat.basic

/-! # IMO 2007 A2 -/

namespace IMOSL
namespace IMO2007A2

/-! ## `nat` version -/
def good' (f : ℕ → ℕ) := ∀ m n : ℕ, f m + f (f n) ≤ f (m + n + 1)



section results

variables {f : ℕ → ℕ} (h : good' f)
include h

private lemma lem1 : monotone f :=
begin
  intros x y h0,
  rw le_iff_exists_add at h0,
  rcases h0 with ⟨c, rfl⟩,
  cases c with c c,
  rw add_zero,
  rw [nat.succ_eq_add_one, ← add_assoc],
  exact le_trans le_self_add (h x c)
end

private lemma lem2 : f 0 = 0 :=
begin
  cases (f 0).eq_zero_or_pos with h0 h0,
  exact h0,
  have h1 := lt_of_lt_of_le (lt_add_of_pos_left _ h0) (h 0 0),
  replace h0 : f 1 ≤ f (f 0) := lem1 h h0,
  rw [zero_add, ← not_le] at h1,
  exfalso; exact h1 h0
end

private lemma lem3 {k d : ℕ} (h0 : f k = k + d + 1) : f d = 0 :=
begin
  replace h := h d k,
  rwa [h0, add_comm k d, add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h
end

private lemma lem4 (n : ℕ) : f n ≤ n + 1 :=
begin
  rw [← not_lt, lt_iff_exists_add],
  rintros ⟨d, h0, h1⟩,
  have h2 : ∀ m : ℕ, f m + (n + 1 + d) ≤ f (m + (n + 1)) :=
  begin
    intros m,
    have h2 := h m n,
    rw [h1, add_assoc m n 1] at h2,
    refine le_trans (add_le_add_left _ _) h2,
    rw ← h1; apply lem1 h,
    rw [h1, add_assoc]; exact le_self_add
  end,

  replace h2 : ∀ j : ℕ, j * (n + 1 + d) ≤ f (j * (n + 1)) :=
  begin
    intros j; induction j with j j_ih,
    rw zero_mul; exact nat.zero_le _,
    rw [nat.succ_mul, nat.succ_mul],
    exact le_trans (add_le_add_right j_ih _) (h2 _)
  end,

  replace h2 := h2 (n + 1),
  cases d with d d,
  exact lt_irrefl 0 h0,
  rw [mul_add, nat.mul_succ _ d, le_iff_exists_add] at h2,
  cases h2 with c h2,
  rw [add_assoc, ← add_assoc _ n 1, add_right_comm, ← add_assoc] at h2,
  replace h2 := lem3 h h2,
  have h3 : n ≤ (n + 1) * d + n + c := by rw add_right_comm; exact le_add_self,
  replace h3 := lem1 h h3,
  rw [h1, h2, nat.le_zero_iff, add_eq_zero_iff] at h3,
  exact ne_of_gt d.succ_pos h3.2
end

end results



section construction

private lemma lem5 (K : ℕ) : good' (λ n, n - K) :=
begin
  intros m n; dsimp only [],
  rw nat.sub_sub; cases le_total n (K + K) with h h,
  rw [nat.sub_eq_zero_of_le h, add_zero, add_assoc],
  exact nat.sub_le_sub_right le_self_add K,
  rw le_iff_exists_add at h,
  rcases h with ⟨c, rfl⟩,
  rw [nat.add_sub_cancel_left, add_right_comm, add_right_comm K K c,
      ← add_assoc, nat.add_sub_cancel, ← add_assoc, add_le_add_iff_right,
      tsub_le_iff_right, add_assoc, add_assoc],
  exact le_self_add
end

private def good_fn (K n : ℕ) := n + ite (K ∣ n.succ) 1 0

private lemma lem6 {K : ℕ} (h : K ≠ 1) (n : ℕ) : good_fn K (good_fn K n) = good_fn K n :=
begin
  unfold good_fn; split_ifs; try { refl },
  rw [nat.succ_eq_add_one, ← nat.dvd_add_iff_right h_1, nat.dvd_one] at h_2,
  exfalso; exact h h_2
end

private lemma lem7 {K : ℕ} (h : K ≠ 1) : good' (good_fn K) :=
begin
  intros m n; rw lem6 h,
  unfold good_fn,
  rw [add_add_add_comm, add_assoc (m + n), add_le_add_iff_left],
  by_cases h0 : K ∣ m.succ,
  rw [if_pos h0, add_le_add_iff_left],
  by_cases h1 : K ∣ n.succ,
  rw [if_pos h1, if_pos],
  rw [← nat.succ_eq_add_one, ← nat.add_succ, ← nat.succ_add],
  exact dvd_add h0 h1,
  rw if_neg h1; exact nat.zero_le _,
  rw [if_neg h0, zero_add],
  refine le_trans _ le_self_add,
  by_cases h1 : K ∣ n.succ,
  rw if_pos h1,
  rw if_neg h1; exact zero_le_one
end

end construction



/-- Final solution, `nat` version, `N ≠ 0` -/
theorem final_solution_nat_ne_zero {N : ℕ} (h : 0 < N) (k : ℕ) :
  (∃ f : ℕ → ℕ, good' f ∧ f N = k) ↔ k ≤ N + 1 :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,
  { rcases h0 with ⟨f, h0, rfl⟩,
    exact lem4 h0 N },
  { rw [le_iff_lt_or_eq, nat.lt_succ_iff] at h0,
    rcases h0 with h0 | rfl,
    exact ⟨λ n, n - (N - k), lem5 _, nat.sub_sub_self h0⟩,
    refine ⟨good_fn N.succ, lem7 (ne_of_gt (nat.succ_lt_succ h)), _⟩,
    rw [good_fn, if_pos (dvd_refl N.succ)] }
end

/-- Final solution, `nat` version, `N = 0` -/
theorem final_solution_nat_zero (k : ℕ) : (∃ f : ℕ → ℕ, good' f ∧ f 0 = k) ↔ k = 0 :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,
  rcases h0 with ⟨f, h0, rfl⟩,
  exacts [lem2 h0, ⟨λ n, n - 0, lem5 0, by rw [nat.sub_zero, h0]⟩]
end







/-! ## `pnat` version -/
def good (f : ℕ+ → ℕ+) := ∀ m n : ℕ+, f m + f (f n) ≤ f (m + n) + 1

private lemma good_good' (f : ℕ+ → ℕ+) : good f ↔ good' (λ x, (f x.succ_pnat).nat_pred) :=
begin
  unfold good good',
  conv_rhs { find (_ ≤ _) {
    rw [pnat.succ_pnat_nat_pred, ← add_le_add_iff_right 1, pnat.nat_pred_add_one, add_assoc,
        pnat.nat_pred_add_one, ← add_le_add_iff_right 1, add_right_comm, pnat.nat_pred_add_one,
        ← pnat.add_coe, ← pnat.one_coe, ← pnat.add_coe, pnat.coe_le_coe, pnat.one_coe] } },
  suffices : ∀ m n : ℕ, (m + n + 1).succ_pnat = m.succ_pnat + n.succ_pnat,
  { refine ⟨λ h m n, _, λ h m n, _⟩,
    rw this; exact h m.succ_pnat n.succ_pnat,
    replace h := h m.nat_pred n.nat_pred,
    rw this at h; simp only [pnat.succ_pnat_nat_pred] at h,
    exact h },
  intros m n,
  rw [← pnat.coe_inj, pnat.add_coe],
  simp only [nat.succ_pnat_coe, nat.succ_eq_add_one],
  rw [add_assoc, add_add_add_comm]
end

private lemma good'_good (f : ℕ → ℕ) : good' f ↔ good (λ x, (f x.nat_pred).succ_pnat) :=
  by rw [good_good', iff_iff_eq]; congr

private lemma good_exists_iff (N k : ℕ+) :
  (∃ f : ℕ+ → ℕ+, good f ∧ f N = k) ↔ (∃ f : ℕ → ℕ, good' f ∧ f N.nat_pred = k.nat_pred) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨f, h, rfl⟩,
    rw good_good' at h,
    exact ⟨_, h, by rw pnat.succ_pnat_nat_pred⟩ },
  { rcases h with ⟨f, h, h0⟩,
    rw good'_good at h,
    exact ⟨_, h, by rw [h0, pnat.succ_pnat_nat_pred]⟩ }
end



/-- Final solution, `pnat` version, `N ≠ 1` -/
theorem final_solution_pnat_ne_one {N : ℕ+} (h : 1 < N) (k : ℕ+) :
  (∃ f : ℕ+ → ℕ+, good f ∧ f N = k) ↔ k ≤ N + 1 :=
begin
  rw [good_exists_iff, final_solution_nat_ne_zero, pnat.nat_pred_add_one, pnat.nat_pred,
      tsub_le_iff_right, ← pnat.one_coe, ← pnat.add_coe, pnat.coe_le_coe],
  change 0 with (1 : ℕ+).nat_pred,
  rwa pnat.nat_pred_lt_nat_pred
end

/-- Final solution, `pnat` version, `N = 1` -/
theorem final_solution_pnat_one (k : ℕ+) :
  (∃ f : ℕ+ → ℕ+, good f ∧ f 1 = k) ↔ k = 1 :=
begin
  rw good_exists_iff; change (1 : ℕ+).nat_pred with 0,
  rw final_solution_nat_zero; change 0 with (1 : ℕ+).nat_pred,
  rw pnat.nat_pred_inj
end

end IMO2007A2
end IMOSL
