import extra.seq_max algebra.group_power.order data.pi.algebra

/-! # IMO 2017 A4 -/

namespace IMOSL
namespace IMO2017A4

variables {G : Type*} [linear_ordered_add_comm_group G]

def good1 (D : ℕ) (a : ℕ → G) :=
  ∀ i j : ℕ, D ≤ i + j → a (i + j + 1) ≤ -(a i + a j)

def good2 (D : ℕ) (a : ℕ → G) :=
  ∀ n : ℕ, D ≤ n → ∃ i j : ℕ, i + j = n ∧ a (n + 1) = -(a i + a j)



lemma abs_le_max_seq_max (a : ℕ → G) (n : ℕ) :
  |a n| ≤ max (2 • extra.seq_max a n) (extra.seq_max (-a) n) :=
  le_max_iff.mpr $ (le_total 0 (a n)).imp
    (λ h, (abs_of_nonneg h).trans_le $ let h0 := extra.le_seq_max_self a n in
      h0.trans $ (two_nsmul $ extra.seq_max a n).symm ▸ le_add_of_nonneg_left $ h.trans h0)
    (λ h, (abs_of_nonpos h).trans_le $ extra.le_seq_max_self _ n)

lemma good1_bdd_above {D : ℕ} {a : ℕ → G} (h : good1 D a) {n : ℕ} (h0 : D ≤ n) :
  a (n + 1) ≤ extra.seq_max (-a) n - extra.seq_max a n :=
  exists.elim (extra.exists_map_eq_seq_max a n) $ λ j h1,
  exists.elim (nat.exists_eq_add_of_le' h1.1) $ λ i h2,
  h2.symm ▸ (h i j $ h0.trans_eq h2).trans $ (neg_add' _ _).trans_le $
    let h3 := sub_le_sub (extra.le_seq_max_of_le (-a) $ i.le_add_right j)
      (h1.2.trans $ congr_arg (extra.seq_max a) h2).ge in h3

lemma good1_seq_max {D : ℕ} {a : ℕ → G} (h : good1 D a) {n : ℕ} (h0 : D ≤ n) :
  extra.seq_max a (n + 1) ≤ max (extra.seq_max a n) (extra.seq_max (-a) n - extra.seq_max a n) :=
  max_le_max (le_refl _) (good1_bdd_above h h0)

lemma good2_bdd_below {D : ℕ} {a : ℕ → G} (h : good2 D a) {n : ℕ} (h0 : D ≤ n) :
  -a (n + 1) ≤ 2 • extra.seq_max a n :=
  exists.elim (h n h0) $ λ i h0, exists.elim h0 $ λ j h0,
    (neg_eq_iff_eq_neg.mpr h0.2).trans_le $ (two_nsmul $ extra.seq_max a n).symm ▸
      h0.1 ▸ add_le_add (extra.le_seq_max_of_le a $ i.le_add_right j)
        (extra.le_seq_max_of_le a $ j.le_add_left i)

lemma good2_seq_max {D : ℕ} {a : ℕ → G} (h : good2 D a) {n : ℕ} (h0 : D ≤ n) :
  extra.seq_max (-a) (n + 1) ≤ max (extra.seq_max (-a) n) (2 • extra.seq_max a n) :=
    max_le_max (le_refl _) (good2_bdd_below h h0)



section seq_max

variables {b c : ℕ → G} {D : ℕ} (h : ∀ n, D ≤ n → b (n + 1) ≤ max (b n) (c n - b n))
  (h0 : ∀ n, D ≤ n → c (n + 1) ≤ max (c n) (2 • b n)) (h1 : monotone b)
include h h0 h1

lemma c_bdd {K : ℕ} (h2 : D ≤ K) (h3 : c K ≤ 2 • b K) :
  b (K + 1) = b K ∧ c (K + 1) ≤ 2 • b (K + 1) :=
suffices b K = b (K + 1), from ⟨this.symm, (h0 K h2).trans_eq $ this ▸ max_eq_right h3⟩,
(h1 K.le_succ).antisymm $ (h K h2).trans_eq $ max_eq_left $
  sub_left_le_of_le_add $ h3.trans_eq $ two_nsmul _

lemma c_succ_eq_self_of_b_bdd (h2 : monotone c) {K : ℕ} (h3 : D ≤ K) (h4 : 2 • b K < c K) :
  c (K + 1) = c K :=
  ((h0 K h3).trans_eq $ max_eq_left_of_lt h4).antisymm (h2 K.le_succ)

lemma c_succ_eq_D_of_b_bdd (h2 : monotone c) {K : ℕ} (h3 : D ≤ K) :
  2 • b K < c K → c (K + 1) = c D :=
  let X : ∀ {M : ℕ}, D ≤ M → 2 • b M < c M → c (M + 1) = c M :=
    λ M, c_succ_eq_self_of_b_bdd h h0 h1 h2 in
  nat.le_induction (X D.le_refl) (λ n h4 h5 h6, (X (h4.trans n.le_succ) h6).trans $
    h5 $ lt_of_not_le $ λ h7, h6.not_le (c_bdd h h0 h1 h4 h7).2) K h3

lemma max_two_nsmul_b_and_c_bdd' (h2 : monotone c) {n : ℕ} (h3 : D ≤ n) :
  max (2 • b n) (c n) ≤ max (2 • b D) (2 • (c D - b D)) :=
nat.le_induction
(max_le (le_max_left _ _) $ le_max_of_two_nsmul_le_add $ nsmul_add (b D) (c D - b D) 2 ▸
  (congr_arg2 _ rfl (add_sub_cancel'_right _ _).symm).le)
(λ K h4 h5, (le_or_lt (c K) (2 • b K)).elim
  (λ h6, h5.trans_eq' $ let h7 := c_bdd h h0 h1 h4 h6 in
    (max_eq_left h7.2).trans $ h7.1.symm ▸ (max_eq_left h6).symm)
  (λ h6, (le_max_right _ _).trans' $
    let h7 := c_succ_eq_self_of_b_bdd h h0 h1 h2 h4 h6,
      h8 := le_sub_left_of_add_le $ h6.le.trans_eq' (two_nsmul _).symm in
    (nsmul_mono_left 2 $ sub_le_sub
      (h7.symm.trans $ c_succ_eq_D_of_b_bdd h h0 h1 h2 h4 h6).le (h1 h4)).trans' $
    (max_le_max (nsmul_mono_left 2 $ (h K h4).trans_eq $ max_eq_right h8) h7.le).trans_eq
    (max_eq_left $ (sub_le_iff_le_add.mp $ sub_le_sub_left h8 _).trans_eq (two_nsmul _).symm)))
  n h3

lemma max_two_nsmul_b_and_c_bdd (h2 : monotone c) (n : ℕ) :
  max (2 • b n) (c n) ≤ max (2 • b D) (2 • (c D - b D)) :=
  (le_total D n).elim (max_two_nsmul_b_and_c_bdd' h h0 h1 h2) $
    λ h3, (max_le_max (nsmul_mono_left 2 $ h1 h3) (h2 h3)).trans
      (max_two_nsmul_b_and_c_bdd' h h0 h1 h2 D.le_refl)

end seq_max





/-- Final solution -/
theorem final_solution {D : ℕ} {a : ℕ → G} (h : good1 D a) (h0 : good2 D a) (n : ℕ) :
  |a n| ≤ max (2 • extra.seq_max a D) (2 • (extra.seq_max (-a) D - extra.seq_max a D)) :=
  (abs_le_max_seq_max a n).trans $ max_two_nsmul_b_and_c_bdd (λ m h1, good1_seq_max h h1)
    (λ m h1, good2_seq_max h0 h1) (extra.seq_max_mono a) (extra.seq_max_mono (-a)) n

end IMO2017A4
end IMOSL
