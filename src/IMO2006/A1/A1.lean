import algebra.order.archimedean

/-! # IMO 2006 A1 -/

namespace IMOSL
namespace IMO2006A1

open function

lemma int_seq_not_bdd_above_of_partial_strict_mono
  {a : ℕ → ℤ} (h : ∀ n, ∃ k, n ≤ k ∧ a n < a k) (c : ℤ) : ∃ n, c < a n :=
  (lt_or_le c (a 0)).elim (λ h0, ⟨0, h0⟩) $ c.le_induction
    (exists.elim (h 0) $ λ k h1, ⟨k, h1.2⟩)
    (λ d h0 h1, exists.elim h1 $ λ m h1, exists.elim (h m) $
      λ k h2, ⟨k, (int.add_one_le_of_lt h1).trans_lt h2.2⟩)

lemma int_seq_eventually_const_of_mono_bdd_above
  {a : ℕ → ℤ} (h : monotone a) {c : ℤ} (h0 : ∀ n : ℕ, a n ≤ c) :
  ∃ N, ∀ n, N ≤ n → a n = a N :=
  classical.by_contradiction $ λ h1, exists.elim
    (@int_seq_not_bdd_above_of_partial_strict_mono a
      (λ N, exists.elim (not_forall.mp $ not_exists.mp h1 N) $ λ n h2,
        let h2 := not_imp.mp h2 in ⟨n, h2.1, lt_of_le_of_ne' (h h2.1) h2.2⟩) c)
    (λ n, not_lt_of_le $ h0 n)



variables {R : Type*} [linear_ordered_ring R] [floor_ring R]

lemma lt_add_one_of_floor_le {r s : R} (h : ⌊r⌋ ≤ ⌊s⌋) : r - s < 1 :=
  sub_lt_comm.mp $ (int.sub_one_lt_floor r).trans_le (int.le_floor.mp h)

lemma abs_sub_lt_one_of_floor_eq {r s : R} (h : ⌊r⌋ = ⌊s⌋) : |r - s| < 1 :=
  abs_sub_lt_iff.mpr $ ⟨lt_add_one_of_floor_le (le_of_eq h),
    lt_add_one_of_floor_le (le_of_eq h.symm)⟩

lemma exists_one_le_mul_pow_of_pos [archimedean R]
  {r : R} (h : 0 < r) {n : ℤ} (h0 : 1 < n) (c : R) : ∃ k : ℕ, c ≤ n ^ k * r :=
  exists.elim (archimedean.arch c h) $ λ k h1, ⟨k, h1.trans $
    by rw [← int.nat_abs_of_nonneg (le_of_lt $ int.one_pos.trans h0),
      int.cast_coe_nat, ← nat.cast_pow, ← nsmul_eq_mul];
    exact nsmul_le_nsmul (le_of_lt h) (le_of_lt $ k.lt_pow_self $
      int.nat_abs_lt_nat_abs_of_nonneg_of_lt int.one_nonneg h0)⟩

lemma floor_eq_neg_one_of_Ioo_neg_one_zero {r : R} (h : -1 < r) (h0 : r < 0) : ⌊r⌋ = -1 :=
  by rw [int.floor_eq_iff, int.cast_neg, int.cast_one, neg_add_self];
    exact ⟨le_of_lt h, h0⟩







/-! ## Start of the problem -/

def f (r : R) := (⌊r⌋ : R) * int.fract r



lemma f_nonneg_of_nonneg {r : R} (h : 0 ≤ r) : 0 ≤ f r :=
  mul_nonneg (int.cast_nonneg.mpr $ int.floor_nonneg.mpr h) (int.fract_nonneg r)

lemma f_iter_nonneg {r : R} (h : 0 ≤ r) : ∀ n, 0 ≤ (f^[n] r)
| 0 := h
| (n+1) := (f_nonneg_of_nonneg $ f_iter_nonneg n).trans_eq
    (iterate_succ_apply' f n r).symm

lemma f_iter_large_floor_nonpos : ∀ (n : ℕ) (r : R), ⌊r⌋ ≤ n → ⌊(f^[n]) r⌋ ≤ 0
| 0 r h := h.trans_eq nat.cast_zero
| (n+1) r h := (congr_arg int.floor $ iterate_succ_apply f n r).trans_le $
    f_iter_large_floor_nonpos n (f r) $ int.le_of_lt_add_one $ int.floor_lt.mpr $
    (le_or_lt (⌊r⌋ : R) 0).elim
      (λ h0, (mul_nonpos_of_nonpos_of_nonneg h0 $ int.fract_nonneg _).trans_lt $
        int.cast_pos.mpr $ int.lt_add_one_of_le n.cast_nonneg)
      (λ h0, (mul_lt_of_lt_one_right h0 $ int.fract_lt_one _).trans_le $
        int.cast_le.mpr $ h.trans_eq n.cast_succ)

lemma f_iter_large_eq_zero_of_nonneg {r : R} (h : 0 ≤ r) {n : ℕ} (h0 : ⌊r⌋ ≤ n) :
  f^[n + 1] r = 0 :=
  (iterate_succ_apply' f n r).trans $
    mul_eq_zero_of_left (int.cast_eq_zero.mpr $ le_antisymm
      (f_iter_large_floor_nonpos n r h0) (int.floor_nonneg.mpr $ f_iter_nonneg h n)) _

lemma f_iter_floor_abs_succ_eq_zero_of_nonneg {r : R} (h : 0 ≤ r) :
  f^[⌊r⌋.nat_abs + 1] r = 0 :=
  f_iter_large_eq_zero_of_nonneg h int.le_nat_abs

lemma f_zero : f (0 : R) = 0 :=
  mul_eq_zero_of_left (int.cast_eq_zero.mpr int.floor_zero) _



lemma f_nonpos_of_nonpos {r : R} (h : r ≤ 0) : f r ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg ((int.floor_le r).trans h) (int.fract_nonneg r)

lemma f_iter_nonpos {r : R} (h : r ≤ 0) : ∀ n : ℕ, f^[n] r ≤ 0
| 0 := h
| (n+1) := (iterate_succ_apply' f n r).trans_le $ f_nonpos_of_nonpos $ f_iter_nonpos n

lemma f_floor_ge_of_nonpos {r : R} (h : r ≤ 0) : ⌊r⌋ ≤ ⌊f r⌋ :=
  int.le_floor.mpr $ le_mul_of_le_one_right
    (int.cast_nonpos.mpr $ int.floor_nonpos h) (le_of_lt $ int.fract_lt_one r)

lemma exists_f_iter_floor_const {r : R} (h : r ≤ 0) :
  ∃ N, ∀ n, N ≤ n → ⌊(f^[n]) r⌋ = ⌊(f^[N]) r⌋ :=
  int_seq_eventually_const_of_mono_bdd_above
    (monotone_nat_of_le_succ $ λ n,
      (f_floor_ge_of_nonpos $ f_iter_nonpos h n).trans_eq $
        congr_arg int.floor (iterate_succ_apply' f n r).symm)
    (λ n, int.floor_nonpos $ f_iter_nonpos h n)

lemma f_sub_abs_eq_of_floor_eq {n : ℤ} {a b : R} (h : ⌊a⌋ = n) (h0 : ⌊b⌋ = n) :
  |f a - f b| = |n| * |a - b| :=
  by rw [f, int.fract, h, f, int.fract, h0, ← mul_sub, sub_sub_sub_cancel_right, abs_mul]

lemma fixed_pt_of_iter_floor_const_lt_neg_one [archimedean R]
  {r : R} (h : ⌊r⌋ < -1) (h0 : ∀ n, ⌊(f^[n]) r⌋ = ⌊r⌋) : f r = r :=
begin
  rw [← sub_eq_zero, ← abs_nonpos_iff, ← not_lt],
  replace h := lt_abs.mpr (or.inr $ lt_neg_of_lt_neg h),
  intros h1; cases exists_one_le_mul_pow_of_pos h1 h 1 with k h2,
  revert h2; refine not_le_of_lt (lt_of_lt_of_eq' (abs_sub_lt_one_of_floor_eq $
    (h0 k.succ).trans (h0 k).symm) _),
  
  ---- Induction on `k`
  induction k with k h2,
  rw [pow_zero, one_mul, iterate_one, iterate_zero_apply],
  rw [pow_succ, mul_assoc, h2, iterate_succ_apply', iterate_succ_apply',
      f_sub_abs_eq_of_floor_eq (h0 k.succ) (h0 k), iterate_succ_apply', int.cast_abs]
end

lemma f_floor_eq_neg_one {r : R} (h : ⌊r⌋ = -1) : f r = -(r + 1) :=
  by rw [f, int.fract, h, int.cast_neg, int.cast_one, sub_neg_eq_add, neg_one_mul]

lemma f_floor_eq_neg_one' {r : R} (h : -1 < r) (h0 : r < 0) : f r = -(r + 1) :=
  f_floor_eq_neg_one $ floor_eq_neg_one_of_Ioo_neg_one_zero h h0

lemma f_iter_two_fixed_pt {r : R} (h : -1 < r) (h0 : r < 0) : f (f r) = r :=
  by rw [f_floor_eq_neg_one' h h0, f_floor_eq_neg_one' (neg_lt_neg $ add_lt_of_neg_left 1 h0)
    (neg_lt_zero.mpr $ neg_lt_iff_pos_add.mp h), neg_eq_iff_eq_neg, ← eq_sub_iff_add_eq, neg_add']

lemma f_neg_one : f (-1 : R) = 0 :=
  mul_eq_zero_of_right _ $ int.fract_neg_eq_zero.mpr int.fract_one



/-- Final solution -/
theorem final_solution [archimedean R] (r : R) : ∃ N : ℕ, f (f (f^[N] r)) = (f^[N]) r :=
begin
  cases le_total 0 r with h h,

  ---- `r ≥ 0`
  { refine ⟨⌊r⌋.nat_abs + 1, _⟩,
    rw [f_iter_floor_abs_succ_eq_zero_of_nonneg h, f_zero, f_zero] },

  ---- `r ≤ 0`
  { cases exists_f_iter_floor_const h with N h0,
    replace h := f_iter_nonpos h N,
    rw le_iff_eq_or_lt at h; cases h with h h,
    refine ⟨N, _⟩; rw [h, f_zero, f_zero],
    cases lt_or_le ⌊(f^[N]) r⌋ (-1) with h1 h1,

    -- `⌊f^N(r)⌋ < -1`
    { refine ⟨N, _⟩; suffices : f (f^[N] r) = (f^[N]) r,
        rw [this, this],
      refine fixed_pt_of_iter_floor_const_lt_neg_one h1 (λ n, _),
      rw ← iterate_add_apply; exact h0 (n + N) le_add_self },

    -- `f^N(r) ≥ -1`
    rw [int.le_floor, int.cast_neg, int.cast_one, le_iff_eq_or_lt] at h1,
    cases h1 with h1 h1,
    refine ⟨N + 1, _⟩; rw [iterate_succ_apply', ← h1, f_neg_one, f_zero, f_zero],
    exact ⟨N, f_iter_two_fixed_pt h1 h⟩ }
end







/- ## Extra -/

lemma nonpos_of_fixed_pt_iter_two {r : R} (h : f (f r) = r) : r ≤ 0 :=
  le_of_lt_or_eq $ (lt_or_le r 0).imp_right $ λ h0,
    by rw [← iterate_one f, ← iterate_add_apply] at h;
      rw [← iterate_fixed h (⌊r⌋.nat_abs + 1), ← iterate_mul, two_mul, iterate_add_apply,
        f_iter_floor_abs_succ_eq_zero_of_nonneg h0, iterate_fixed f_zero]

lemma fixed_pt_of_fixed_pt_iter_two {r : R} (h : f (f r) = r) (h0 : ⌊r⌋ < -1) : f r = r :=
begin
  have h1 : r ≤ 0 := le_of_lt ((int.floor_lt.mp h0).trans $
    int.cast_lt_zero.mpr $ int.neg_succ_lt_zero 0),
  replace h1 : ⌊r⌋ = ⌊f r⌋ := le_antisymm (f_floor_ge_of_nonpos h1)
    ((f_floor_ge_of_nonpos $ f_nonpos_of_nonpos h1).trans_eq $ congr_arg int.floor h),
  replace h1 := f_sub_abs_eq_of_floor_eq rfl h1.symm,
  rw [h, abs_sub_comm r] at h1,
  refine eq_of_abs_sub_eq_zero (eq_zero_of_mul_eq_self_left
    (ne_of_gt $ lt_abs.mpr $ or.inr _) h1.symm),
  rwa [lt_neg, ← int.cast_one, ← int.cast_neg, int.cast_lt]
end

lemma fixed_pt_equiv_special_formula {r : R} : f r = r ↔ (-⌊r⌋ + 1 : R) * r = -⌊r⌋ ^ 2 :=
  by rw [f, int.fract, mul_sub, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add',
    ← sub_one_mul, ← sq, ← neg_eq_iff_eq_neg, ← neg_mul, neg_add', neg_neg]

lemma fixed_pt_special_formula {r : R} (h : f r = r) : ∃ n : ℕ, (n + 1 : R) * r = -n ^ 2 :=
  exists.elim (int.exists_eq_neg_of_nat $ int.floor_nonpos $
    nonpos_of_fixed_pt_iter_two $ (congr_arg f h).trans h) $
  λ n h0, ⟨n, by rwa [fixed_pt_equiv_special_formula, h0,
    int.cast_neg, int.cast_coe_nat, neg_neg, neg_sq] at h⟩

lemma special_formula_imp_fixed_pt {r : R} {n : ℕ} (h : (n + 1 : R) * r = -n ^ 2) : f r = r :=
  suffices ⌊r⌋ = -n, by rwa [fixed_pt_equiv_special_formula,
    this, int.cast_neg, int.cast_coe_nat, neg_neg, neg_sq],
begin
  have h0 : 0 < (n : R) + 1 := add_pos_of_nonneg_of_pos n.cast_nonneg one_pos,
  rw [int.floor_eq_iff, int.cast_neg, int.cast_coe_nat]; split,
  
  ---- `-n ≤ r`
  rw [← mul_le_mul_left h0, h, mul_neg, neg_le_neg_iff, sq,
    add_one_mul, le_add_iff_nonneg_right]; exact n.cast_nonneg,
  
  ---- `r < -n + 1`
  rw [← mul_lt_mul_left h0, h, neg_lt, ← mul_neg, neg_add', neg_neg,
      ← (commute.one_right (n : R)).sq_sub_sq, sub_lt_self_iff, one_pow]; exact one_pos
end

/-- Final solution, extra part -/
theorem final_solution_extra {r : R} :
  f (f r) = r ↔ (∃ n : ℕ, (n + 1 : R) * r = -n ^ 2) ∨ (-1 < r ∧ r < 0) :=
⟨λ h, (lt_or_le ⌊r⌋ (-1)).elim
  (λ h0, or.inl $ fixed_pt_special_formula $ fixed_pt_of_fixed_pt_iter_two h h0)
  (λ h0, begin
    rw [int.le_floor, int.cast_neg, int.cast_one, le_iff_eq_or_lt] at h0,
    rcases h0 with rfl | h0,
    rw [f_neg_one, f_zero, zero_eq_neg] at h; exact absurd h one_ne_zero,
    refine (eq_or_lt_of_le $ nonpos_of_fixed_pt_iter_two h).imp (λ h1, _) (and.intro h0),
    exact ⟨0, by rw [h1, mul_zero, nat.cast_zero, sq, mul_zero, neg_zero]⟩
  end),
λ h, h.elim (λ h, exists.elim h $ λ n h, let h := special_formula_imp_fixed_pt h in
  (congr_arg f h).trans h) (λ h, f_iter_two_fixed_pt h.1 h.2)⟩

end IMO2006A1
end IMOSL
