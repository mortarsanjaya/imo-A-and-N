import data.nat.parity algebra.big_operators.intervals algebra.big_operators.order

/-! # IMO 2017 C1 -/

namespace IMOSL
namespace IMO2017C1

open finset

/-- The lattice rectangle `Ico a (a + l) × Ico b (b + w)`-/
def lattice_rect (q : (ℕ × ℕ) × (ℕ × ℕ)) : finset (ℕ × ℕ) :=
  Ico q.1.1 (q.1.1 + q.2.1) ×ˢ Ico q.1.2 (q.1.2 + q.2.2)

/-- The weight of a finset in `ℕ × ℕ` -/
def weight (S : finset (ℕ × ℕ)) := S.sum (λ p, ite (even (p.1 + p.2)) 1 (-1 : ℤ))



lemma sum_ite_neg_one_one_alt_range (a : ℕ) :
  ∀ n : ℕ, (range n).sum (λ x, ite (even (a + x)) (1 : ℤ) (-1)) =
    ite (even n) 0 (ite (even a) 1 (-1))
| 0 := (sum_range_zero _).trans (if_pos even_zero).symm
| 1 := (sum_range_one _).trans (if_neg nat.not_even_one).symm
| (n+2) :=
  by rw [sum_range_succ, sum_range_succ, ← ite_not, ← eq_add_neg_iff_add_eq,
    sum_ite_neg_one_one_alt_range, apply_ite has_neg.neg, ← add_assoc];
    exact congr_arg2 has_add.add
      (if_congr (by rw [nat.even_add, iff_true_right even_two]) rfl rfl)
      (if_congr nat.even_add_one.symm rfl rfl)

lemma sum_ite_neg_one_one_alt_Ico (a b n : ℕ) :
  (Ico a (a + n)).sum (λ x, ite (even (b + x)) (1 : ℤ) (-1)) =
    ite (even n) 0 (ite (even (b + a)) 1 (-1)) :=
  by rw [sum_Ico_eq_sum_range, nat.add_sub_cancel_left, ← sum_ite_neg_one_one_alt_range];
    exact sum_congr rfl (λ x _, if_congr
      (iff_of_eq $ congr_arg even (add_assoc b a x).symm) rfl rfl)

lemma rect_weight_eq (q : (ℕ × ℕ) × (ℕ × ℕ)) : weight (lattice_rect q)
  = ite (even q.2.1 ∨ even q.2.2) 0 (ite (even (q.1.1 + q.1.2)) 1 (-1 : ℤ)) :=
begin
  rw [weight, lattice_rect, sum_product],
  simp_rw sum_ite_neg_one_one_alt_Ico,
  by_cases h : even q.2.2,

  ---- `q.2.2` is even
  conv_lhs { congr, skip, funext, rw if_pos h },
  rw [if_pos (or.inr h), sum_const_zero],

  ---- `q.2.2` is odd
  conv_lhs { congr, skip, funext, rw [if_neg h, add_comm] },
  rw [sum_ite_neg_one_one_alt_Ico, add_comm],
  exact if_congr (or_iff_left h).symm rfl rfl
end

lemma rect_weight_pos_iff {q : (ℕ × ℕ) × (ℕ × ℕ)} :
  0 < weight (lattice_rect q) ↔ (odd q.2.1 ∧ odd q.2.2) ∧ even (q.1.1 + q.1.2) :=
begin
  rw [nat.odd_iff_not_even, nat.odd_iff_not_even,
      ← not_or_distrib, rect_weight_eq],
  by_cases h : even q.2.1 ∨ even q.2.2,
  rw [if_pos h, lt_self_iff_false, iff_true_intro h, not_true, false_and],
  rw [if_neg h, iff_true_intro h, true_and],
  by_cases h0 : even (q.1.1 + q.1.2),
  rw [if_pos h0, iff_true_intro int.one_pos, iff_true_intro h0],
  rw [if_neg h0, neg_pos, iff_false_intro (not_lt_of_lt int.one_pos), iff_false_intro h0]
end





/-- Final solution -/
theorem final_solution {ι : Type*} {I : finset ι} {Q : ι → (ℕ × ℕ) × (ℕ × ℕ)}
  (h : (I : set ι).pairwise_disjoint (lattice_rect ∘ Q))
  {m n : ℕ} (h0 : odd m ∧ odd n)
  (h1 : lattice_rect ⟨⟨0, 0⟩, ⟨m, n⟩⟩ = I.disj_Union (lattice_rect ∘ Q) h) :
  ∃ (i : ι) (h : i ∈ I), (odd (Q i).2.1 ∧ odd (Q i).2.2) ∧ even ((Q i).1.1 + (Q i).1.2) :=
begin
  let f := λ p : ℕ × ℕ, ite (even (p.1 + p.2)) 1 (-1 : ℤ),
  replace h0 : 0 < (lattice_rect ((0, 0), m, n)).sum f :=
    rect_weight_pos_iff.mpr ⟨h0, even_zero⟩,
  replace h1 : 0 < I.sum (λ i, (lattice_rect $ Q i).sum f) :=
    lt_of_lt_of_eq h0 ((sum_congr h1 $ λ p _, rfl).trans (sum_disj_Union I _ h)),
  rcases exists_lt_of_sum_lt (lt_of_eq_of_lt sum_const_zero h1) with ⟨i, h2, h3⟩,
  exact ⟨i, h2, rect_weight_pos_iff.mp h3⟩
end

end IMO2017C1
end IMOSL
