import algebra.order.archimedean

/-! # IMO 2006 A1 -/

namespace IMOSL
namespace IMO2006A1

open function




private lemma int_seq_eventually_constant_of_mono_bdd_above
  {a : ℕ → ℤ} (h : monotone a) {c : ℤ} (h0 : ∀ n : ℕ, a n ≤ c) :
  ∃ (d : ℤ) (_ : d ≤ c) (N : ℕ), ∀ n : ℕ, N ≤ n → a n = d :=
begin
  suffices : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n.succ ≤ a n,
  { rcases this with ⟨N, h1⟩,
    refine ⟨a N, h0 N, N, nat.le_induction (by refl) _⟩,
    intros n h2 h3; rw ← h3; clear h3,
    exact le_antisymm (h1 n h2) (h n.le_succ) },
  
  contrapose! h0,
  cases exists_lt (a 0) with d h1,
  cases lt_or_le c d with h2 h2,
  exact ⟨0, lt_trans h2 h1⟩,
  revert h2 c; refine int.le_induction ⟨0, h1⟩ _,
  rintros x - ⟨k, h3⟩; clear h1 d,
  replace h0 := h0 k,
  rcases h0 with ⟨n, h0, h1⟩,
  exact ⟨n.succ, lt_of_le_of_lt (le_trans h3 (h h0)) h1⟩
end



section basic_results

variables {R : Type*} [linear_ordered_ring R] [floor_ring R]

def f (r : R) := (⌊r⌋ : R) * int.fract r

private lemma f_nonneg_of_nonneg {r : R} (h : 0 ≤ r) : 0 ≤ f r :=
  mul_nonneg (int.cast_nonneg.mpr $ int.le_floor.mpr $ le_of_eq_of_le int.cast_zero h)
    (int.fract_nonneg r)

private lemma f_iterate_nonneg {r : R} (h : 0 ≤ r) : ∀ n : ℕ, 0 ≤ (f^[n] r)
| 0 := h
| (n+1) := by rw iterate_succ'; exact f_nonneg_of_nonneg (f_iterate_nonneg n)

private lemma f_floor_eq_zero {r : R} (h : ⌊r⌋ = 0) : f r = 0 :=
  by rw [f, h, int.cast_zero, zero_mul]

private lemma f_floor_lt_floor_of_ge_one {r : R} (h : 1 ≤ r) : ⌊f r⌋ < ⌊r⌋ :=
  by rw [int.floor_lt, f, ← sub_pos, ← mul_one_sub];
    exact mul_pos (int.cast_pos.mpr $ int.floor_pos.mpr h) (sub_pos.mpr $ int.fract_lt_one r)


private lemma f_nonpos_of_nonpos {r : R} (h : r ≤ 0) : f r ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (le_trans (int.floor_le r) h) (int.fract_nonneg r)

private lemma f_iterate_nonpos {r : R} (h : r ≤ 0) : ∀ n : ℕ, f^[n] r ≤ 0
| 0 := h
| (n+1) := by rw iterate_succ'; exact f_nonpos_of_nonpos (f_iterate_nonpos n)

private lemma f_floor_ge_of_nonpos {r : R} (h : r ≤ 0) : ⌊r⌋ ≤ ⌊f r⌋ :=
  by rw [int.le_floor, f, ← sub_nonpos, ← mul_one_sub];
    exact mul_nonpos_of_nonpos_of_nonneg (int.cast_nonpos.mpr $ int.floor_nonpos h)
      (sub_nonneg.mpr $ le_of_lt $ int.fract_lt_one r)

private lemma f_Ioo_neg_one_zero {r : R} (h : -1 < r) (h0 : r < 0) : f r = -1 - r :=
begin
  suffices h1 : ⌊r⌋ = -1,
    rw [f, int.fract, h1, int.cast_neg, int.cast_one, neg_one_mul, neg_sub],
  rw [int.floor_eq_iff, int.cast_neg, int.cast_one, neg_add_self],
  exact ⟨le_of_lt h, h0⟩
end

private lemma f2_Ioo_neg_one_zero {r : R} (h : -1 < r) (h0 : r < 0) : (f^[2]) r = r :=
  by rw [iterate_succ, comp_app, iterate_one, f_Ioo_neg_one_zero h h0];
    exact (f_Ioo_neg_one_zero (lt_sub_iff_add_lt.mpr $ add_lt_iff_neg_left.mpr h0)
      $ sub_neg.mpr h).trans (sub_sub_self (-1) r)

private lemma f_special_value {k : ℕ} {r : R} (h : (k + 1 : R) * r = -k ^ 2) : f r = r :=
begin
  suffices : ⌊r⌋ = -k,
    rw [f, int.fract, this, int.cast_neg, int.cast_coe_nat, neg_mul, sub_neg_eq_add,
        mul_add, ← sq, neg_add, ← h, add_one_mul, neg_add_cancel_left],
  have h0 : 0 < (k : R) + 1 := add_pos_of_nonneg_of_pos k.cast_nonneg one_pos,
  rw [int.floor_eq_iff, int.cast_neg, int.cast_coe_nat]; split,
  rw [← mul_le_mul_left h0, h, add_one_mul, mul_neg, ← sq, add_le_iff_nonpos_right, neg_nonpos],
  exact k.cast_nonneg,
  rw [← mul_lt_mul_left h0, h, add_one_mul, mul_add_one, mul_neg, add_assoc,
      ← sq, lt_add_iff_pos_right, ← add_assoc, add_neg_self, zero_add],
  exact one_pos
end

private lemma f_floor_iterate_const [archimedean R]
  {k : ℕ} (h : 1 < k) {r : R} (h0 : ∀ n : ℕ, ⌊(f^[n]) r⌋ = -k) : (k + 1 : R) * r = -k ^ 2 :=
begin
  ---- Setup
  rw eq_neg_iff_add_eq_zero,
  generalize h1 : (k + 1 : R) * r + k ^ 2 = c,

  ---- For any `n : ℕ`, `(k + 1) (f^n(r) - r) = ((-k)^n - 1) c`
  replace h1 : ∀ n : ℕ, (k + 1 : R) * ((f^[n]) r - r) = ((-k) ^ n - 1) * c :=
  begin
    intros n,
    rw sub_one_mul; nth_rewrite 1 ← h1,
    rw [eq_sub_iff_add_eq, mul_sub, ← add_assoc, sub_add_cancel],
    induction n with n n_ih,
    rw [iterate_zero, id.def, h1, pow_zero, one_mul],
    rw [iterate_succ', comp_app, pow_succ _ n, mul_assoc, ← n_ih],
    replace h0 := h0 n,
    generalize_hyp : (f^[n]) r = x at h0 n_ih ⊢,
    rw [f, int.fract, h0, int.cast_neg, int.cast_coe_nat, sub_neg_eq_add,
        neg_mul, neg_mul, mul_neg, ← sub_eq_neg_add, ← neg_sub, neg_inj, mul_add,
        ← sq, mul_add, add_sub_assoc, ← sub_one_mul, add_sub_cancel, mul_add,
        add_left_inj, ← mul_assoc, ← mul_assoc, add_one_mul, mul_add_one]
  end,

  ---- For any `n : ℕ`, `|f^n(r) - r| < 1`
  replace h0 : ∀ n : ℕ, |(f^[n]) r - r| < 1 :=
  begin
    intros n,
    have h2 := h0 n,
    replace h0 := h0 0,
    rw [iterate_zero, id.def] at h0,
    rw [int.floor_eq_iff, int.cast_neg, int.cast_coe_nat] at h0 h2,
    rw [abs_sub_lt_iff, sub_lt_iff_lt_add, sub_lt_iff_lt_add, add_comm, add_comm (1 : R)],
    exact ⟨lt_of_lt_of_le h2.2 (add_le_add_right h0.1 _),
           lt_of_lt_of_le h0.2 (add_le_add_right h2.1 _)⟩
  end,

  ---- Final step
  by_contra h2; rw [← ne.def, ← abs_pos] at h2,
  replace h2 := archimedean.arch (k + 1 : R) h2,
  cases h2 with n h2,
  replace h1 := congr_arg has_abs.abs (h1 n),
  revert h1; have h1 : 0 < (k : R) + 1 := add_pos_of_nonneg_of_pos k.cast_nonneg one_pos,
  rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt h1)],
  refine ne_of_lt (lt_of_lt_of_le ((mul_lt_mul_left h1).mpr (h0 n)) _),
  rw mul_one; refine le_trans h2 _,
  clear h0 h1 h2,
  rw nsmul_eq_mul,
  refine mul_le_mul_of_nonneg_right (le_trans _ (abs_sub_abs_le_abs_sub _ _)) (abs_nonneg c),
  rw [abs_one, abs_pow, abs_neg, nat.abs_cast, le_sub_iff_add_le,
      ← nat.cast_succ, ← nat.cast_pow, nat.cast_le, nat.succ_le_iff],
  exact nat.lt_pow_self h n
end

end basic_results







/-- Final solution, case `x ≥ 0` -/
theorem final_solution_x_nonneg {R : Type*} [linear_ordered_ring R] [floor_ring R]
  {x : R} (h : 0 ≤ x) : ∀ n : ℕ, ⌊x⌋ < n → (f^[n]) x = 0 :=
begin
  ---- Start with casting `⌊x⌋` to `K : ℕ`
  lift ⌊x⌋ to ℕ using by rwa [int.le_floor, int.cast_zero] with K h0,

  ---- Reduce to showing `0 ≤ ⌊f^n(x)⌋ ≤ K - n` for all `n ≤ K`
  suffices : ∀ n : ℕ, n ≤ K → ⌊(f^[n]) x⌋ ≤ ↑(K - n),
  { replace this := this K (le_refl K),
    rw [nat.sub_self, nat.cast_zero] at this,
    simp_rw [nat.cast_lt, ← nat.succ_le_iff],
    refine nat.le_induction _ (λ n h1 h2, _),
    rw [iterate_succ', comp_app, f_floor_eq_zero (le_antisymm this _)],
    rw [int.le_floor, int.cast_zero]; exact f_iterate_nonneg h K,
    rw [iterate_succ', comp_app, h2, f, int.floor_zero, int.cast_zero, zero_mul] },
  
  ---- Proceed by induction, with trivial base case
  intros n h1; induction n with n n_ih,
  rw [iterate_zero, id.def, ← h0, nat.sub_zero],
  replace n_ih := n_ih (le_trans n.le_succ h1),
  rw [iterate_succ', comp_app],
  have h2 := f_iterate_nonneg h n,
  rw [← int.cast_zero, ← int.le_floor, le_iff_eq_or_lt, eq_comm] at h2,
  cases h2 with h2 h2,
  rw [f_floor_eq_zero h2, int.floor_zero]; exact nat.cast_nonneg _,
  rw [← int.add_one_le_iff, zero_add, int.le_floor, int.cast_one] at h2,
  replace n_ih := lt_of_lt_of_le (f_floor_lt_floor_of_ge_one h2) n_ih,
  rw ← int.le_sub_one_iff at n_ih,
  convert n_ih; clear h0 h2 n_ih,
  rw le_iff_exists_add at h1,
  rcases h1 with ⟨c, rfl⟩,
  rw [nat.add_sub_cancel_left, nat.succ_eq_add_one, add_assoc,
      nat.add_sub_cancel_left, nat.cast_add, nat.cast_one, add_tsub_cancel_left]
end



/-- Final solution, case `x ≤ 0` -/
theorem final_solution_x_nonpos {R : Type*} [linear_ordered_ring R] [floor_ring R] [archimedean R]
  {x : R} (h : x ≤ 0) :
  (∃ N k : ℕ, (k + 1 : R) * (f^[N] x) = -k ^ 2) ∨ (∃ N : ℕ, -1 < (f^[N]) x ∧ (f^[N]) x < 0) :=
begin
  ---- First obtain some `N` such that `(⌊f^n(x)⌋)_{n ≥ 0}` stabilizes
  obtain ⟨d, h0, N, h1⟩ : ∃ (d : ℤ) (_ : d ≤ 0) (N : ℕ), ∀ n : ℕ, N ≤ n → ⌊(f^[n]) x⌋ = d :=
  begin
    have h0 : ∀ n : ℕ, ⌊(f^[n]) x⌋ ≤ 0 := λ n, int.floor_nonpos (f_iterate_nonpos h n),
    convert int_seq_eventually_constant_of_mono_bdd_above _ h0,
    intros m; refine nat.le_induction (by refl) _,
    simp only []; intros n h0 h1,
    rw [iterate_succ', comp_app],
    exact le_trans h1 (f_floor_ge_of_nonpos (f_iterate_nonpos h n))
  end,

  ---- Remove the case `d = 0` and `d = -1`
  rw [le_iff_eq_or_lt, ← int.le_sub_one_iff, zero_sub, le_iff_eq_or_lt] at h0,
  rcases h0 with rfl | rfl | h0,
  left; refine ⟨N + 1, 0, _⟩,
  rw [nat.cast_zero, zero_add, one_mul, zero_pow two_pos, neg_zero, iterate_succ', comp_app],
  exact f_floor_eq_zero (h1 N (le_refl N)),
  have h2 := h1 N (le_refl N),
  rw [int.floor_eq_iff, le_iff_lt_or_eq] at h2,
  rcases h2 with ⟨h2 | h2, h3⟩,
  rw [int.cast_neg, int.cast_one] at h2 h3,
  rw neg_add_self at h3; right; exact ⟨N, h2, h3⟩,
  exfalso; clear h3,
  replace h1 := h1 N.succ N.le_succ,
  rw [iterate_succ', comp_app, ← h2, f, int.fract, int.floor_int_cast,
      sub_self, mul_zero, int.floor_zero, zero_eq_neg] at h1,
  revert h1; exact one_ne_zero,

  ---- Work on the case `d < -1`
  left; rw lt_neg at h0,
  lift -d to ℕ using le_trans zero_le_one (le_of_lt h0) with k h2,
  rw eq_neg_iff_eq_neg at h2; subst h2,
  rw nat.one_lt_cast at h0,
  refine ⟨N, k, f_floor_iterate_const h0 (λ n, _)⟩,
  replace h1 := h1 (n + N) le_add_self,
  rwa [iterate_add, comp_app] at h1
end



/-- Final solution -/
theorem final_solution {R : Type*} [linear_ordered_ring R] [floor_ring R] [archimedean R] (x : R) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f^[n + 2]) x = (f^[n]) x :=
begin
  cases le_total 0 x with h h,

  ---- Case 1: `x ≥ 0`
  { lift ⌊x⌋ to ℕ using by rwa [int.le_floor, int.cast_zero] with K h0,
    replace h := final_solution_x_nonneg h,
    simp_rw [← h0, nat.cast_lt, ← nat.succ_le_iff] at h,
    exact ⟨K + 1, λ n h1, by rw [h n h1, h (n + 2) (le_add_right h1)]⟩ },
  
  ---- Case 2: `x ≤ 0`
  { replace h := final_solution_x_nonpos h,
    rcases h with ⟨N, k, h⟩ | ⟨N, h, h0⟩,

    -- Subcase 2.1: `(k + 1) f^N(x) = -k^2` for some `N k : ℕ`
    { replace h := f_special_value h; clear k,
      suffices : ∀ {n : ℕ}, N ≤ n → (f^[n]) x = (f^[N]) x,
        exact ⟨N, λ n h0, by rw [this h0, this (le_add_right h0)]⟩,
      refine nat.le_induction (by refl) _,
      rintros n - h0; rw [iterate_succ', comp_app, h0, h] },

    -- Subcase 2.2: `-1 < f^N(x) < 0` for some `N : ℕ`
    { replace h := f2_Ioo_neg_one_zero h h0; clear h0,
      refine ⟨N, λ n h0, _⟩,
      rw le_iff_exists_add at h0; rcases h0 with ⟨c, rfl⟩,
      simp_rw [add_comm N, add_right_comm c N, iterate_add, comp_app, h] } }
end

end IMO2006A1
end IMOSL
