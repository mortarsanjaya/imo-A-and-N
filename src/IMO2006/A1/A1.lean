import algebra.order.floor

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



variables {R : Type*} [linear_ordered_ring R] [floor_ring R]

def f (r : R) := (⌊r⌋ : R) * int.fract r

private lemma f_nonneg_of_nonneg {r : R} (h : 0 ≤ r) : 0 ≤ f r :=
  mul_nonneg (by rwa [int.cast_nonneg, int.le_floor, int.cast_zero]) (int.fract_nonneg r)

private lemma f_iterate_nonneg {r : R} (h : 0 ≤ r) (n : ℕ) : 0 ≤ (f^[n] r) :=
begin
  induction n with n n_ih,
  rw [iterate_zero, id.def]; exact h,
  rw [iterate_succ', comp_app]; exact f_nonneg_of_nonneg n_ih
end

private lemma f_floor_eq_zero {r : R} (h : ⌊r⌋ = 0) : f r = 0 :=
  by rw [f, h, int.cast_zero, zero_mul]

private lemma f_floor_lt_floor_of_ge_one {r : R} (h : 1 ≤ r) : ⌊f r⌋ < ⌊r⌋ :=
begin
  rw [int.floor_lt, f, ← sub_pos, ← mul_one_sub]; apply mul_pos,
  rwa [int.cast_pos, ← int.add_one_le_iff, zero_add, int.le_floor, int.cast_one],
  rw sub_pos; exact int.fract_lt_one r
end


private lemma f_nonpos_of_nonpos {r : R} (h : r ≤ 0) : f r ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (le_trans (int.floor_le r) h) (int.fract_nonneg r)

private lemma f_iterate_nonpos {r : R} (h : r ≤ 0) (n : ℕ) : f^[n] r ≤ 0 :=
begin
  induction n with n n_ih,
  rw [iterate_zero, id.def]; exact h,
  rw [iterate_succ', comp_app]; exact f_nonpos_of_nonpos n_ih
end

private lemma f_floor_ge_of_nonpos {r : R} (h : r ≤ 0) : ⌊r⌋ ≤ ⌊f r⌋ :=
begin
  rw [int.le_floor, f, ← sub_nonpos, ← mul_one_sub]; apply mul_nonpos_of_nonpos_of_nonneg,
  rw int.cast_nonpos; exact int.floor_nonpos h,
  rw sub_nonneg; exact le_of_lt (int.fract_lt_one r)
end

private lemma f_between_neg_one_and_zero {r : R} (h : -1 < r) (h0 : r < 0) :
  f r = -1 - r ∧ (f^[2]) r = r :=
begin
  revert r h h0,
  suffices : ∀ {r : R}, -1 < r → r < 0 → f r = -1 - r,
  { intros r h1 h2,
    have h3 := this h1 h2,
    refine ⟨h3, _⟩,
    rw ← sub_neg at h1; rw [← add_right_neg (1 : R), ← neg_lt_sub_iff_lt_add] at h2,
    rw [iterate_succ, iterate_one, comp_app, h3, this h2 h1, sub_sub_cancel] },
  
  intros r h h0,
  suffices : ⌊r⌋ = -1,
    rw [f, int.fract, this, int.cast_neg, int.cast_one, neg_one_mul, neg_sub],
  rw [int.floor_eq_iff, int.cast_neg, int.cast_one, neg_add_self],
  exact ⟨le_of_lt h, h0⟩
end

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

private lemma f_floor_iterate_const {k : ℕ} (h : 1 < k) {r : R} (h0 : ∀ n : ℕ, ⌊(f^[n]) r⌋ = -k) :
  (k + 1 : R) * r = -k ^ 2 :=
begin
  sorry
end







/-- Final solution, case `x ≥ 0` -/
theorem final_solution_x_nonneg {x : R} (h : 0 ≤ x) : ∀ n : ℕ, ⌊x⌋ < n → (f^[n]) x = 0 :=
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
theorem final_solution_x_nonpos {x : R} (h : x ≤ 0) :
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
theorem final_solution (x : R) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f^[n + 2]) x = (f^[n]) x :=
begin
  cases le_total 0 x with h h,

  ---- Case 1: `x ≥ 0`
  { lift ⌊x⌋ to ℕ using by rwa [int.le_floor, int.cast_zero] with K h0,
    replace h := final_solution_x_nonneg h,
    simp_rw [← h0, nat.cast_lt, ← nat.succ_le_iff] at h,
    exact ⟨K + 1, λ n h1, by rw [h n h1, h (n + 2) (le_add_right h1)]⟩ },
  
  ---- Case 2: `x ≤ 0`
  replace h := final_solution_x_nonpos h,
  rcases h with ⟨N, k, h⟩ | ⟨N, h, h0⟩,
  { replace h := f_special_value h; clear k,
    suffices : ∀ {n : ℕ}, N ≤ n → (f^[n]) x = (f^[N]) x,
      exact ⟨N, λ n h0, by rw [this h0, this (le_add_right h0)]⟩,
    refine nat.le_induction (by refl) _,
    rintros n - h0; rw [iterate_succ', comp_app, h0, h] },
  { replace h := f_between_neg_one_and_zero h h0,
    rcases h with ⟨-, h⟩; clear h0,
    refine ⟨N, λ n h0, _⟩,
    rw le_iff_exists_add at h0; rcases h0 with ⟨c, rfl⟩,
    simp_rw [add_comm N, add_right_comm c N, iterate_add, comp_app, h] }
end

end IMO2006A1
end IMOSL
