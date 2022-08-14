import data.int.basic tactic.ring

/-! # IMO 2014 N2 -/

namespace IMOSL
namespace IMO2014N2

def good (x y : ℤ) := 7 * x ^ 2 - 13 * (x * y) + 7 * y ^ 2 = (|x - y| + 1) ^ 3

def good_pair (m : ℤ) : ℤ × ℤ := (m ^ 3 + 2 * m ^ 2 - m - 1, m ^ 3 + m ^ 2 - 2 * m - 1)



private lemma good_swap {x y : ℤ} (h : good x y) : good y x :=
  by unfold good at h ⊢; rw [abs_sub_comm, ← h, sub_add_comm, mul_comm x y]

private lemma good_y_le_x {x y : ℤ} (h : good x y) (h0 : y ≤ x) : ∃ m : ℤ, (x, y) = good_pair m :=
begin
  sorry
end

private lemma good_pair_is_good (m : ℤ) : good (good_pair m).1 (good_pair m).2 :=
begin
  suffices : 0 ≤ (m + 1) * m,
  { unfold good good_pair; ring_nf,
    rw abs_eq_self.mpr this; ring },
  sorry
end



/-- Final solution -/
theorem final_solution (x y : ℤ) :
  good x y ↔ (∃ m : ℤ, (x, y) = good_pair m) ∨ (∃ m : ℤ, (y, x) = good_pair m) :=
begin
  split,
  { intros h,
    cases le_total y x with h0 h0,
    left; exact good_y_le_x h h0,
    right; exact good_y_le_x (good_swap h) h0 },
  { rintros (⟨m, h⟩ | ⟨m, h⟩),
    all_goals {
      have h0 := good_pair_is_good m,
      rwa ← h at h0 },
    exact good_swap h0 }
end

end IMO2014N2
end IMOSL
