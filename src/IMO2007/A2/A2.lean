import data.pnat.basic

/-! # IMO 2007 A2 -/

namespace IMOSL
namespace IMO2007A2

/-! ## `nat` version -/
def good' (f : ℕ → ℕ) := ∀ m n : ℕ, f m + f (f n) ≤ f (m + n + 1)

/-! ## `pnat` version -/
def good (f : ℕ+ → ℕ+) := ∀ m n : ℕ+, f m + f (f n) ≤ f (m + n) + 1



/-! ## Correspondence between `good` and `good'` -/
section correspondence

private lemma good_iff_good' (f : ℕ+ → ℕ+) : good f ↔ good' (λ x, (f x.succ_pnat).nat_pred) :=
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

private lemma correspondence (N k : ℕ+) :
  (∃ f : ℕ+ → ℕ+, good f ∧ f N = k) ↔ (∃ f : ℕ → ℕ, good' f ∧ f N.nat_pred = k.nat_pred) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨f, h, rfl⟩,
    rw good_iff_good' at h,
    refine ⟨_, h, _⟩,
    rw pnat.succ_pnat_nat_pred },
  { rcases h with ⟨f, h, h0⟩,
    replace h : good (λ x, (f x.nat_pred).succ_pnat) := by rw good_iff_good'; convert h,
    refine ⟨_, h, _⟩,
    rw [h0, pnat.succ_pnat_nat_pred] }
end

end correspondence



/-! ## Main results -/

private lemma good'_monotone {f : ℕ → ℕ} (h : good' f) : monotone f :=
begin
  intros x y h0,
  rw le_iff_exists_add at h0,
  rcases h0 with ⟨c, rfl⟩,
  cases c with c c,
  rw add_zero,
  rw [nat.succ_eq_add_one, ← add_assoc],
  exact le_trans le_self_add (h x c)
end

private lemma good'_val_bound {f : ℕ → ℕ} (h : good' f) (N : ℕ) : f N ≤ N + 1 :=
begin
  generalize hK : N + 1 = K,
  rw [← not_lt, ← nat.add_one_le_iff]; intros h0,

  -- We prove that `f(mK) ≥ mf(K)` for all `m : ℕ`.
  have h1 : ∀ m : ℕ, m * f K ≤ f (m * K) :=
  begin
    intros m; induction m with m m_ih,
    rw [zero_mul, zero_mul]; exact zero_le _,
    rw [nat.succ_mul, nat.succ_mul, ← hK, ← add_assoc, hK],
    exact le_trans (add_le_add m_ih (good'_monotone h (nat.le_of_succ_le h0))) (h _ _)
  end,

  -- For the case `m = K`, get some `d ≥ N` such that `f(K^2) = K^2 + d + 1`
  replace h1 : ∃ d : ℕ, N ≤ d ∧ f (K * K) = K * K + d + 1 :=
  begin
    replace h0 := le_trans h0 (good'_monotone h N.le_succ),
    rw [nat.succ_eq_add_one, hK] at h0,
    replace h1 := le_trans (nat.mul_le_mul_left _ h0) (h1 K),
    rw [mul_add_one, le_iff_exists_add] at h1,
    cases h1 with c h1,
    refine ⟨N + c, le_self_add, _⟩,
    rw [add_assoc, add_right_comm, hK, ← add_assoc, ← h1]
  end,

  -- Finishing
  rcases h1 with ⟨d, h2, h3⟩,
  replace hK := h d (K * K),
  rw [add_comm d, h3, add_le_iff_nonpos_left, nonpos_iff_eq_zero] at hK,
  revert hK; exact ne_of_gt (lt_of_lt_of_le K.succ_pos (le_trans h0 (good'_monotone h h2)))
end

private lemma sub_right_good' (c : ℕ) : good' (λ n, n - c) :=
begin
  intros m n; dsimp only [],
  cases le_total n c with h h,
  rw [nat.sub_eq_zero_of_le h, nat.zero_sub, add_zero, add_assoc],
  exact nat.sub_le_sub_right le_self_add _,
  rw le_iff_exists_add at h; rcases h with ⟨d, rfl⟩,
  rw [nat.add_sub_cancel_left, add_right_comm, add_comm c, ← add_assoc, nat.add_sub_cancel],
  exact add_le_add (le_trans (nat.sub_le m c) m.le_succ) (nat.sub_le d c)
end

private lemma add_bin_div_good' {K : ℕ} (h : 1 < K) : good' (λ n, n + ite (K ∣ n + 1) 1 0) :=
begin
  intros m n; dsimp only [],
  rw [add_add_add_comm, ← add_assoc m, add_assoc, add_assoc (m + n), add_le_add_iff_left],
  by_cases h0 : K ∣ n + 1,
  { simp_rw [if_pos h0, add_assoc m, add_left_comm m, nat.dvd_add_right h0, ← add_assoc,
             add_le_iff_nonpos_right, nonpos_iff_eq_zero, ite_eq_right_iff],
    intros h1; exfalso; exact ne_of_gt h (nat.eq_one_of_dvd_one h1) },
  { rw [if_neg h0, zero_add, add_zero, if_neg h0, add_zero],
    exact le_trans (ite_le_sup 1 0 _) le_self_add }
end







/-- Final solution, `nat` version, `N = 0` -/
theorem final_solution_nat_zero (k : ℕ) : (∃ f : ℕ → ℕ, good' f ∧ f 0 = k) ↔ k = 0 :=
begin
  symmetry; refine ⟨λ h, ⟨λ _, 0, λ m n, _, h.symm⟩, λ h, _⟩,
  simp only [add_zero],
  rcases h with ⟨f, h, rfl⟩,
  by_contra h0; rw [← ne.def, ← pos_iff_ne_zero] at h0,
  refine not_le_of_lt (lt_of_lt_of_le (lt_add_of_pos_left _ h0) (h 0 0)) _,
  rw ← nat.succ_le_iff at h0,
  exact good'_monotone h h0
end

/-- Final solution, `nat` version, `N > 0` -/
theorem final_solution_nat_ne_zero {N : ℕ} (h : 0 < N) (k : ℕ) :
  (∃ f : ℕ → ℕ, good' f ∧ f N = k) ↔ k ≤ N + 1 :=
begin
  refine ⟨λ h0, _, λ h0, _⟩,
  rcases h0 with ⟨f, h0, rfl⟩,
  exact good'_val_bound h0 N,
  rw [le_iff_lt_or_eq, nat.lt_succ_iff, le_iff_exists_add] at h0,
  rcases h0 with ⟨c, rfl⟩ | rfl,
  exact ⟨λ n, n - c, sub_right_good' c, nat.add_sub_cancel k c⟩,
  exact ⟨_, add_bin_div_good' (nat.succ_lt_succ h), by rw if_pos (dvd_refl _)⟩
end

/-- Final solution, `pnat` version, `N = 1` -/
theorem final_solution_pnat_one (k : ℕ+) :
  (∃ f : ℕ+ → ℕ+, good f ∧ f 1 = k) ↔ k = 1 :=
begin
  rw correspondence; change (1 : ℕ+).nat_pred with 0,
  rw final_solution_nat_zero; change 0 with (1 : ℕ+).nat_pred,
  rw pnat.nat_pred_inj
end

/-- Final solution, `pnat` version, `N > 1` -/
theorem final_solution_pnat_ne_one {N : ℕ+} (h : 1 < N) (k : ℕ+) :
  (∃ f : ℕ+ → ℕ+, good f ∧ f N = k) ↔ k ≤ N + 1 :=
begin
  rw [correspondence, final_solution_nat_ne_zero, pnat.nat_pred_add_one, pnat.nat_pred,
      tsub_le_iff_right, ← pnat.one_coe, ← pnat.add_coe, pnat.coe_le_coe],
  change 0 with (1 : ℕ+).nat_pred,
  rwa pnat.nat_pred_lt_nat_pred
end

end IMO2007A2
end IMOSL
