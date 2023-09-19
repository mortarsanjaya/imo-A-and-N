import IMO2022.C6.C6_basic data.nat.factorization.basic

/-! # IMO 2022 C6 -/

namespace IMOSL
namespace IMO2022C6

open multiset

def good (X : multiset ℕ) (n : ℕ) :=
  ∃ Y : multiset ℕ, Y.card ≤ n ∧ is_reachable X Y





lemma good_zero_of_sum_eq_zero {X : multiset ℕ} (h : X.sum = 0) : good X 0 :=
  ⟨0, le_refl 0, is_reachable.of_sum_eq_zero h⟩

lemma sum_eq_zero_of_good_zero {X : multiset ℕ} (h : good X 0) : X.sum = 0 :=
  exists.elim h $ λ Y h, h.2.sum_eq.trans $ congr_arg multiset.sum $
    card_eq_zero.mp $ nat.eq_zero_of_le_zero h.1

lemma good_zero_iff {X : multiset ℕ} : good X 0 ↔ X.sum = 0 :=
  ⟨sum_eq_zero_of_good_zero, good_zero_of_sum_eq_zero⟩


lemma good_one_of_ord_compl2_dvd_mem {X : multiset ℕ} (h : X.sum ≠ 0)
  (h0 : ∀ x, x ∈ X → ord_compl[2] X.sum ∣ x) : good X 1 :=
  ⟨{X.sum}, le_refl 1, let h1 := X.sum.ord_proj_mul_ord_compl_eq_self 2 in
    (is_reachable.sum_eq_two_pow_mul_to_singleton_of_dvd_all
      (nat.ord_compl_pos 2 h).ne.symm h1.symm h0).trans $
    is_reachable.congr $ congr_arg singleton h1⟩

lemma ord_compl2_dvd_mem_of_good_one {X : multiset ℕ} (h : X.sum ≠ 0) (h0 : good X 1) :
  ∀ x, x ∈ X → ord_compl[2] X.sum ∣ x :=
  is_reachable.odd_dvd_sum_imp_of_singleton_right
    (nat.odd_iff.mpr $ nat.two_dvd_ne_zero.mp $ nat.not_dvd_ord_compl nat.prime_two h)
    (exists.elim h0 $ λ Y h0, h0.2.trans $
      is_reachable.congr $ h0.2.card_le_one_right_eq h h0.1)
    (X.sum.ord_compl_dvd 2)

lemma good_one_iff_of_sum_ne_zero {X : multiset ℕ} (h : X.sum ≠ 0) :
  good X 1 ↔ ∀ x, x ∈ X → ord_compl[2] X.sum ∣ x :=
  ⟨ord_compl2_dvd_mem_of_good_one h, good_one_of_ord_compl2_dvd_mem h⟩


lemma good_two (X : multiset ℕ) : good X 2 :=
  is_reachable.exists_right_card_le_two X





/-- Final solution -/
theorem final_solution (X : multiset ℕ) :
  is_least (good X) $ ite (X.sum = 0) 0 (ite (∀ x, x ∈ X → ord_compl[2] X.sum ∣ x) 1 2) :=
begin
  cases em (X.sum = 0) with h h,
  rw if_pos h; exact ⟨good_zero_of_sum_eq_zero h, λ c _, c.zero_le⟩,
  rw if_neg h; have h0 : ¬good X 0 := λ h0, h (sum_eq_zero_of_good_zero h0),
  
  cases em (∀ x, x ∈ X → ord_compl[2] X.sum ∣ x) with h1 h1,
  rw if_pos h1; refine ⟨good_one_of_ord_compl2_dvd_mem h h1, 
    λ c h2, nat.pos_of_ne_zero $ λ h3, h0 $ h3 ▸ h2⟩,

  rw if_neg h1; refine ⟨good_two X, λ c h2, le_of_not_lt $ λ h3, _⟩,
  rw [nat.lt_succ_iff, le_iff_lt_or_eq, nat.lt_one_iff] at h3,
  exact h3.elim (λ h3, h0 $ h3 ▸ h2)
    (λ h3, h1 $ ord_compl2_dvd_mem_of_good_one h $ h3 ▸ h2)
end

end IMO2022C6
end IMOSL
