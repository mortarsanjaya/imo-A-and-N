import algebra.group.defs data.finset.lattice

/-! # IMO 2007 A1 (P1) -/

namespace IMOSL
namespace IMO2007A1

open finset

variables {G : Type*} [linear_ordered_add_comm_group G] (a : ℕ → G) (n : ℕ)

/-- Final solution, part 1 -/
theorem final_solution_part1 {x : ℕ → G} (h : monotone x) :
  ∀ {k m : ℕ}, k ≤ m → m ≤ n →
    a k - a m ≤ 2 • (range n.succ).sup' nonempty_range_succ (λ i, |x i - a i|) :=
let L := (range n.succ).sup' nonempty_range_succ (λ i, |x i - a i|) in
λ k m h0 h1, by calc
  a k - a m ≤ (a k - a m) - (x k - x m) :
    (le_sub_self_iff _).mpr $ sub_nonpos_of_le $ h h0
  ... = -(x k - a k) + (x m - a m) :
    by rw [neg_sub, sub_sub_sub_comm, sub_sub_eq_add_sub, add_sub_assoc]
  ... ≤ |x k - a k| + |x m - a m| :
    add_le_add (neg_le_abs_self _) (le_abs_self _)
  ... ≤ L + L :
    let h2 : ∀ k, k ≤ n → |x k - a k| ≤ L :=
      λ k h2, le_sup' (λ i, |x i - a i|) (mem_range_succ_iff.mpr h2) in
    add_le_add (h2 k $ h0.trans h1) (h2 m h1)
  ... = 2 • L : (two_nsmul L).symm



/-- Final solution, part 2 -/
theorem final_solution_part2 {g : G} (h : ∀ k m : ℕ, k ≤ m → m ≤ n → a k - a m ≤ 2 • g) :
  ∃ x : ℕ → G, monotone x ∧ (range n.succ).sup' nonempty_range_succ (λ i, |x i - a i|) = g :=
let x : ℕ → G := λ i : ℕ, (range i.succ).sup' nonempty_range_succ a - g in
⟨x, λ i j h0, sub_le_sub_right (sup'_le _ a $ λ t h1, le_sup' _ $
  mem_range.mpr $ (mem_range.mp h1).trans_le $ nat.succ_le_succ h0) g,
begin
  refine le_antisymm (sup'_le _ _ $ λ i h0, abs_le.mpr ⟨_, _⟩)
    (le_sup'_of_le _ (mem_range_succ_iff.mpr n.zero_le) _),
  ---- `-g ≤ x_i - a_i` for all `i ≤ n`
  { rw [neg_le_sub_iff_le_add, sub_add_cancel],
    exact le_sup' a (self_mem_range_succ i) },
  ---- `x_i - a_i ≤ g` for all `i ≤ n`
  { obtain ⟨j, h1, h2⟩ := exists_mem_eq_sup' (nonempty_range_succ : (range i.succ).nonempty) a,
    rw [sub_sub, h2, add_comm, ← sub_sub, sub_le_iff_le_add, ← two_nsmul],
    rw mem_range_succ_iff at h0 h1,
    exact h j i h1 h0 },
  ---- `|x_0 - a_0| ≥ g` via `a_0 - x_0 = g`
  { refine (neg_le_abs_self _).trans_eq' _,
    rw [neg_sub, eq_sub_iff_add_eq', sub_add_cancel,
      sup'_congr _ range_one (λ _ _, rfl), sup'_singleton] }
end⟩

end IMO2007A1
end IMOSL
