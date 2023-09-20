import data.finset.lattice

/-! # IMO 2007 A1 (P1) -/

namespace IMOSL
namespace IMO2007A1

open finset

variables {G : Type*} [linear_ordered_add_comm_group G] (a : ℕ → G) (n : ℕ)

/-- Final solution, part 1 -/
theorem final_solution_part1 {x : ℕ → G} (h : monotone x) :
  ∀ {k m : ℕ}, k ≤ m → m ≤ n →
    a k - a m ≤ 2 • (range n.succ).sup' nonempty_range_succ (λ i, |x i - a i|) :=
λ k m h0 h1, ((le_sub_self_iff _).mpr $ sub_nonpos_of_le (h h0)).trans $
  (sub_sub_sub_comm _ _ _ _).trans_le $ (le_abs_self _).trans $ (abs_sub _ _).trans $
suffices ∀ k, k ≤ n → |a k - x k| ≤ (range n.succ).sup' nonempty_range_succ (λ i, |x i - a i|),
  from (add_le_add (this k $ h0.trans h1) (this m h1)).trans_eq (two_nsmul _).symm,
λ k h2, (abs_sub_comm _ _).trans_le $ le_sup' (λ i, |x i - a i|) (mem_range_succ_iff.mpr h2)



/-- Final solution, part 2 -/
theorem final_solution_part2 {g : G} (h : ∀ k m : ℕ, k ≤ m → m ≤ n → a k - a m ≤ 2 • g) :
  ∃ x : ℕ → G, monotone x ∧ (range n.succ).sup' nonempty_range_succ (λ i, |x i - a i|) = g :=
let x : ℕ → G := λ i : ℕ, (range i.succ).sup' nonempty_range_succ a - g in
⟨x, λ i j h0, sub_le_sub_right (sup'_le _ a $ λ t h1, le_sup' _ $
  mem_range.mpr $ (mem_range.mp h1).trans_le $ nat.succ_le_succ h0) g,
le_antisymm (sup'_le _ _ $ λ i h0, abs_le.mpr
  ⟨neg_le_sub_iff_le_add.mpr $ (sub_add_cancel _ _).ge.trans' $
    le_sup' a (self_mem_range_succ i),
  exists.elim (exists_mem_eq_sup' (nonempty_range_succ : (range i.succ).nonempty) a) $
    λ j h1, (sub_right_comm _ _ _).trans_le $ sub_le_iff_le_add.mpr $ h1.2.symm ▸
      two_nsmul g ▸ h j i (mem_range_succ_iff.mp h1.1) (mem_range_succ_iff.mp h0)⟩)
(le_sup'_of_le _ (mem_range_succ_iff.mpr n.zero_le) $ (neg_le_abs_self _).trans_eq' $ 
  eq.symm $ (neg_sub _ _).trans $ sub_eq_iff_eq_add'.mpr $ eq.symm $
    (sub_add_cancel _ _).trans $ sup'_congr _ range_one $ λ _ _, rfl)⟩

end IMO2007A1
end IMOSL
