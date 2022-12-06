import algebra.order.smul

/-! # IMO 2017 A8, Generalized Version -/

namespace IMOSL
namespace IMO2017A8

variables {G : Type*} [linear_ordered_add_comm_group G]

def good (f : G → G) := ∀ x y : G, f x < f y → f x ≤ x + y ∧ x + y ≤ f y



/-- Final solution, part 1 -/
theorem final_solution_part1 [densely_ordered G] : ∀ f : G → G, good f → monotone f :=
begin
  intros f h x y h0,
  rw le_iff_eq_or_lt at h0,
  rcases h0 with rfl | h0,
  exact le_refl (f x),
  rw ← not_lt; intros h1,

  ---- The claim
  have h2 : ∀ z : G, f y - y < z → z < f x - x → (f z = f x ∨ f z = f y) :=
  begin
    intros z h2 h3,
    rcases lt_trichotomy (f z) (f y) with h4 | h4 | h4,
    exfalso; revert h2,
    rw [imp_false, not_lt, le_sub_iff_add_le],
    exact (h z y h4).elim_right,
    right; exact h4,
    rcases lt_trichotomy (f x) (f z) with h5 | h5 | h5,
    exfalso; revert h3,
    rw [imp_false, not_lt, sub_le_iff_le_add'],
    exact (h x z h5).elim_left,
    left; exact h5.symm,
    exfalso; revert h0,
    rw [imp_false, not_lt, ← add_le_add_iff_left z, add_comm z y],
    exact le_trans (h y z h4).elim_right (h z x h5).elim_left
  end,

  ---- Finishing
  rcases exists_between h0 with ⟨z, h3, h4⟩; clear h0,
  obtain (h5 | h5) : f z = f x ∨ f z = f y :=
  begin
    obtain ⟨h5, h6⟩ := h y x h1,
    rw ← sub_le_iff_le_add' at h5,
    rw ← le_sub_iff_add_le at h6,
    exact h2 z (lt_of_le_of_lt h5 h3) (lt_of_lt_of_le h4 h6)
  end,
  { rcases exists_between h3 with ⟨w, h6, h7⟩; clear h3,
    replace h2 := h2 (f z - w) (sub_lt_sub (by rwa h5) (lt_trans h7 h4))
      (by rw h5; exact sub_lt_sub_left h6 (f x)),
    clear h6; cases h2 with h2 h2,
    { rw ← h2 at h1; replace h1 := (h _ _ h1).elim_right,
      revert h1; rw [h2, ← h5, imp_false, not_le, ← sub_lt_iff_lt_add'],
      exact sub_lt_sub_left (lt_trans h7 h4) (f z) },
    { rw [← h2, ← h5] at h1; replace h1 := (h _ _ h1).elim_right,
      revert h1; rw [imp_false, not_le, ← sub_lt_iff_lt_add],
      exact sub_lt_sub_left h7 (f z) } },
  { rcases exists_between h4 with ⟨w, h6, h7⟩; clear h4,
    replace h2 := h2 (f z - w) (by rw h5; exact sub_lt_sub_left h7 (f y))
      (sub_lt_sub (by rwa h5) (lt_trans h3 h6)),
    clear h7; cases h2 with h2 h2,
    { rw [← h2, ← h5] at h1; replace h1 := (h _ _ h1).elim_left,
      revert h1; rw [imp_false, not_le, ← lt_sub_iff_add_lt'],
      exact sub_lt_sub_left h6 (f z) },
    { rw ← h2 at h1; replace h1 := (h _ _ h1).elim_left,
      revert h1; rw [h2, ← h5, imp_false, not_le, ← lt_sub_iff_add_lt],
      exact sub_lt_sub_left (lt_trans h3 h6) (f z) } }
end



/-- Final solution, part 2 -/
theorem final_solution_part2 (h : ¬densely_ordered G) :
  ∃ f : G → G, ¬monotone f ∧ good f :=
begin
  ---- Change non-dense-ordering criterion with existence of a minimal positive element
  replace h : ∃ g : G, 0 < g ∧ ∀ x : G, 0 < x → g ≤ x :=
  begin
    contrapose! h; refine ⟨λ x y h0, _⟩,
    replace h := h (y - x) (sub_pos_of_lt h0),
    clear h0; rcases h with ⟨g, h, h0⟩,
    exact ⟨g + x, lt_add_of_pos_left x h, lt_sub_iff_add_lt.mp h0⟩
  end,
  
  ---- Given a minimal positive element `g`, construct a good non-monotone function
  rcases h with ⟨g, h, h0⟩,
  refine ⟨λ x : G, ite (x = 0) (2 • g) (ite (x = g) 0 (2 • x)), _, λ x y h1, _⟩,

  ---- Show that the function is not monotone
  { simp_rw [monotone, not_forall],
    refine ⟨0, g, le_of_lt h, _⟩,
    rw [if_pos rfl, if_neg (ne_of_gt h), if_pos rfl, not_le],
    exact smul_pos two_pos h },

  ---- Show that the function is good
  { dsimp only [] at h1 ⊢,
    rcases eq_or_ne 0 x with rfl | hx0,

    -- Case 1: `x = 0`
    { rw if_pos rfl at h1 ⊢,
      rcases eq_or_ne 0 y with rfl | hy0,
      rw if_pos rfl at h1 ⊢,
      exfalso; exact ne_of_lt h1 rfl,
      rcases eq_or_ne g y with rfl | hyg,
      rw [if_neg hy0.symm, if_pos rfl] at h1 ⊢,
      exfalso; exact lt_asymm h1 (smul_pos two_pos h),
      rw [if_neg hy0.symm, if_neg hyg.symm] at h1 ⊢,
      rw [zero_add, and_comm, two_nsmul, le_add_iff_nonneg_left, two_nsmul, ← le_sub_iff_add_le],
      rw smul_lt_smul_iff_of_pos at h1,
      exacts [⟨le_of_lt (lt_trans h h1), h0 _ (sub_pos_of_lt h1)⟩, two_pos] },
    rw if_neg hx0.symm at h1 ⊢,
    rcases eq_or_ne g x with rfl | hxg,

    -- Case 2: `x = g`
    { rw if_pos rfl at h1 ⊢,
      rcases eq_or_ne 0 y with rfl | hy0,
      rw if_pos rfl at h1 ⊢,
      rw add_zero; exact ⟨le_of_lt h, h0 _ h1⟩,
      rcases eq_or_ne g y with rfl | hyg,
      rw [if_neg hy0.symm, if_pos rfl] at h1 ⊢,
      exfalso; exact lt_irrefl 0 h1,
      rw [if_neg hy0.symm, if_neg hyg.symm] at h1 ⊢,
      rw [two_nsmul, add_le_add_iff_right],
      rw smul_pos_iff_of_pos at h1,
      exacts [⟨le_of_lt (add_pos h h1), h0 y h1⟩, two_pos] },

    -- Case 3: `x ∉ {0, g}`
    { rw if_neg hxg.symm at h1 ⊢,
      rcases eq_or_ne 0 y with rfl | hy0,
      rw if_pos rfl at h1 ⊢,
      rw [add_zero, two_nsmul, add_le_iff_nonpos_left, and_iff_left_of_imp],
      contrapose! h1; exact nsmul_le_nsmul_of_le_right (h0 x h1) 2,
      intros h2; exact le_trans h2 (nsmul_nonneg (le_of_lt h) 2),
      rcases eq_or_ne g y with rfl | hyg,
      rw [if_neg hy0.symm, if_pos rfl] at h1 ⊢,
      rw [two_nsmul, add_le_add_iff_left, ← le_neg_iff_add_nonpos_left],
      rw left.nsmul_neg_iff at h1,
      exact ⟨le_of_lt (lt_trans h1 h), h0 _ (neg_pos.mpr h1)⟩,
      exact two_pos,
      rw [if_neg hy0.symm, if_neg hyg.symm] at h1 ⊢,
      rw [two_nsmul, add_le_add_iff_left, two_nsmul, add_le_add_iff_right, and_self],
      rw smul_lt_smul_iff_of_pos at h1,
      exacts [le_of_lt h1, two_pos] } }
end



/-- Final solution, iff version -/
theorem final_solution_iff : densely_ordered G ↔ ∀ f : G → G, good f → monotone f :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  haveI : densely_ordered G := h,
  exact final_solution_part1,
  contrapose! h; simp_rw [and_comm (good _)],
  exact final_solution_part2 h
end

end IMO2017A8
end IMOSL
