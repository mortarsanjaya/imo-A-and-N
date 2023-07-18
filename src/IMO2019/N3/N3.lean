import data.nat.digits

/-! # IMO 2019 N3 -/

namespace IMOSL
namespace IMO2019N3

open list

/- ### Extra lemmas -/

/-- Given `b k : ℤ` with `k ≠ 0`, there exists `m ≠ n` such that `b^m ≡ b^n (mod k)`. -/
lemma exists_ne_pow_eq {k : ℤ} (h : k ≠ 0) (b : ℤ) :
  ∃ m n : ℕ, m ≠ n ∧ k ∣ b ^ m - b ^ n :=
begin
  have h0 : set.maps_to (λ (x : ℕ), b ^ x % k) set.univ (finset.Ico 0 $ |k|) :=
    λ x _, cast (congr_arg2 _ rfl (finset.coe_Ico 0 $ |k|).symm)
      ⟨(b ^ x).mod_nonneg h, (b ^ x).mod_lt h⟩,
  obtain ⟨m, -, n, -, h, h0⟩ :=
    set.infinite_univ.exists_ne_map_eq_of_maps_to h0 (set.to_finite _),
  exact ⟨m, n, h, int.dvd_of_mod_eq_zero (int.mod_eq_mod_iff_mod_sub_eq_zero.mp h0)⟩
end





/- ### Start of the Problem -/

def rootiful (S : set ℤ) := ∀ (x : ℤ) (l : list ℤ),
  (∀ a : ℤ, a ∈ l → a ∈ S) → (∃ a : ℤ, a ∈ l ∧ a ≠ 0) →
    l.foldr (λ a b, a + x * b) 0 = 0 → x ∈ S

lemma univ_rootiful : rootiful set.univ :=
  λ x _ _ _ _, set.mem_univ x

section lemmas

variables {S : set ℤ} (h : rootiful S)
include h

lemma rootiful_neg_one_mem (x : ℤ) (h0 : x ≠ 0) (h1 : x ∈ S) : (-1 : ℤ) ∈ S :=
h (-1) (replicate 2 x)
  (λ a h2, set.mem_of_eq_of_mem (eq_of_mem_replicate h2) h1)
  ⟨x, mem_replicate.mpr ⟨nat.succ_ne_zero 1, rfl⟩, h0⟩
  (add_eq_zero_iff_neg_eq.mpr $ (neg_one_mul x).symm.trans $
    congr_arg _ $ self_eq_add_right.mpr $ mul_zero _)

lemma rootiful_one_mem_of_nat (n : ℕ) (h0 : n ≠ 0) (h1 : (n : ℤ) ∈ S) : (1 : ℤ) ∈ S :=
  let h0 : (n : ℤ) ≠ 0 := nat.cast_ne_zero.mpr h0 in
h 1 (↑n :: replicate n (-1))
  (λ a h2, h2.elim (λ h2, set.mem_of_eq_of_mem h2 h1) $
    λ h2, set.mem_of_eq_of_mem (eq_of_mem_replicate h2) $ rootiful_neg_one_mem h n h0 h1)
  ⟨n, mem_cons_self n _, h0⟩
  (add_eq_zero_iff_neg_eq.mpr $ by conv_rhs { rw one_mul, congr, funext, rw one_mul };
    rw [← sum_eq_foldr, sum_replicate, nsmul_eq_mul, mul_neg_one])

lemma rootiful_one_mem_of_pos (n : ℤ) (h0 : 0 < n) (h1 : n ∈ S) : (1 : ℤ) ∈ S :=
  rootiful_one_mem_of_nat h n.nat_abs (int.nat_abs_ne_zero.mpr $ ne_of_gt h0) $
    cast (congr_arg2 _ (int.eq_nat_abs_of_zero_le h0.le) rfl) h1

lemma rootiful_neg_mem_of_one_mem (h0 : (1 : ℤ) ∈ S) (x : ℤ) (h1 : x ∈ S) : -x ∈ S :=
h (-x) ([x, 1])
  (λ a h2, h2.elim (λ h2, set.mem_of_eq_of_mem h2 h1) $
    λ h2, h2.elim (λ h2, set.mem_of_eq_of_mem h2 h0) (λ h2, absurd h2 $ not_mem_nil a))
  ⟨1, mem_cons_of_mem _ $ mem_singleton_self 1, one_ne_zero' ℤ⟩
  (add_eq_zero_iff_neg_eq.mpr $ (mul_one _).symm.trans $
    congr_arg _ $ self_eq_add_right.mpr $ mul_zero _)

lemma rootiful_neg_mem_of_pos {x : ℤ} (h0 : 0 < x) (h1 : x ∈ S) : -x ∈ S :=
  rootiful_neg_mem_of_one_mem h (rootiful_one_mem_of_pos h x h0 h1) x h1

lemma rootiful_induction_of_nat_dvd_nat {n : ℕ} (h0 : 1 < n) (h1 : ∀ k : ℕ, k < n → (k : ℤ) ∈ S)
  (N : ℕ) (h2 : 0 < N) (h3 : n ∣ N) (h4 : -(N : ℤ) ∈ S) : (n : ℤ) ∈ S :=
exists.elim h3 $ λ K h3, h n (-(N : ℤ) :: (n.digits K).map coe)
  (λ a h5, h5.elim (λ h6, cast (congr_arg2 _ h6.symm rfl) h4) $
    λ h6, exists.elim (mem_map.mp h6) $ λ x h7, cast (congr_arg2 _ h7.2 rfl) $
      h1 x $ nat.digits_lt_base h0 h7.1)
  ⟨-N, mem_cons_self _ _, int.neg_ne_zero_of_ne $ int.coe_nat_ne_zero_iff_pos.mpr h2⟩
  (neg_add_eq_zero.mpr $ (congr_arg coe h3).trans $ (int.coe_nat_mul n K).trans $
    congr_arg _ $ by rw [← int.coe_nat_zero, foldr_map, int.coe_nat_zero,
      ← nat.of_digits_eq_foldr, ← nat.coe_int_of_digits, nat.of_digits_digits n K])

lemma rootiful_induction_of_nat_dvd_int {n : ℕ} (h0 : 1 < n) (h1 : ∀ k : ℕ, k < n → (k : ℤ) ∈ S)
  (N : ℤ) (h2 : N ≠ 0) (h3 : (n : ℤ) ∣ N) (h4 : N ∈ S) : (n : ℤ) ∈ S :=
  rootiful_induction_of_nat_dvd_nat h h0 h1 N.nat_abs
    (int.nat_abs_pos_of_ne_zero h2) (int.coe_nat_dvd_left.mp h3) $
    N.nat_abs_eq.symm.elim (λ h5, cast (congr_arg2 _ h5 rfl) h4)
      (λ h5, rootiful_neg_mem_of_pos h (nat.cast_pos.mpr $ int.nat_abs_pos_of_ne_zero h2) $
        cast (congr_arg2 _ h5 rfl) h4)

lemma rootiful_nat_subset (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S)
  (h2 : ∀ k : ℕ, 0 < k → ∃ N : ℤ, N ≠ 0 ∧ (k : ℤ) ∣ N ∧ N ∈ S) (k : ℕ) : (k : ℤ) ∈ S :=
begin
  induction k using nat.strong_induction_on with k h3,
  cases k, exact h0, cases k, exact h1,
  cases h2 (k + 2) k.succ.succ_pos with N h4,
  exact rootiful_induction_of_nat_dvd_int h
    (nat.succ_lt_succ k.succ_pos) h3 N h4.1 h4.2.1 h4.2.2
end

lemma rootiful_eq_univ (h0 : (0 : ℤ) ∈ S) (h1 : (1 : ℤ) ∈ S)
  (h2 : ∀ k : ℕ, 0 < k → ∃ N : ℤ, N ≠ 0 ∧ (k : ℤ) ∣ N ∧ N ∈ S) : S = set.univ :=
set.eq_univ_of_forall $ λ k, let h3 := rootiful_nat_subset h h0 h1 h2 k.nat_abs in
  (le_or_lt 0 k).elim (λ h4, cast (congr_arg2 _ (int.nat_abs_of_nonneg h4) rfl) h3)
    (λ h4, cast (congr_arg2 _ (neg_eq_iff_eq_neg.mpr $ int.of_nat_nat_abs_of_nonpos h4.le) rfl)
      (rootiful_neg_mem_of_pos h (nat.cast_pos.mpr $ int.nat_abs_pos_of_ne_zero h4.ne) h3))

end lemmas





/-- Final solution -/
theorem final_solution {N : ℤ} (h : 1 < |N|) {S : set ℤ} :
  (rootiful S ∧ ∀ a b : ℕ, N ^ (a + 1) - N ^ (b + 1) ∈ S) ↔ S = set.univ :=
⟨λ h0, rootiful_eq_univ h0.1
  (cast (congr_arg2 _ (sub_self _) rfl) (h0.2 0 0))
  (rootiful_one_mem_of_pos h0.1 (N ^ 2 - N ^ 1)
    (sub_pos.mpr $ (pow_one N).trans_lt $ (le_abs_self _).trans_lt $
      (lt_mul_self h).trans_eq $ (abs_mul_abs_self N).trans (sq N).symm)
    (h0.2 1 0))
  (λ k h1, begin
    obtain ⟨m, n, h2⟩ := exists_ne_pow_eq (ne_of_gt $ nat.cast_pos.mpr h1) N,
    refine ⟨N ^ (m + 1) - N ^ (n + 1), sub_ne_zero_of_ne _, _, h0.2 m n⟩,
    ---- `N^{m + 1} ≠ N^{n + 1}`
    { refine λ h3, h2.1 (nat.succ_injective $ int.pow_right_injective _ h3),
      rwa [← int.nat_abs_one, int.nat_abs_lt_iff_sq_lt, sq_lt_sq, abs_one] },
    ---- `k ∣ N ^{m + 1} - N^{n + 1}`
    { rw [pow_succ, pow_succ, ← mul_sub],
      exact dvd_mul_of_dvd_right h2.2 N }
  end),
λ h0, ⟨cast (congr_arg _ h0.symm) univ_rootiful,
  λ a b, cast (congr_arg _ h0.symm) $ set.mem_univ _⟩⟩

end IMO2019N3
end IMOSL
