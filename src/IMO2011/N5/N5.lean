import group_theory.subgroup.basic data.list.defs

/-! # IMO 2011 N5 (P5) -/

namespace IMOSL
namespace IMO2011N5

variables {G : Type*} [add_group G]

/-! ### Auxiliary lemmas -/

/-- Given integers `a, b > 0`, we have `|a - b| < a + b` -/
lemma abs_sub_lt_add_of_pos {a b : ℤ} (h : 0 < a) (h0 : 0 < b) : |a - b| < a + b :=
  abs_sub_lt_iff.mpr ⟨(sub_lt_self a h0).trans (lt_add_of_pos_right a h0),
    (sub_lt_self b h).trans (lt_add_of_pos_left b h)⟩





/-! ## Start of the problem -/

def good (f : G → ℤ) := ∀ x y : G, f (x - y) ∣ f x - f y





section results

variables {f : G → ℤ} (h : good f)
include h

lemma map_div_map_zero (x : G) : f x ∣ f 0 :=
  dvd_sub_self_left.mp $ (dvd_of_eq $ congr_arg f (sub_zero x).symm).trans (h x 0)

lemma map_neg_dvd_map_self (x : G) : f (-x) ∣ f x :=
  (dvd_sub_right $ map_div_map_zero h (-x)).mp $ zero_sub x ▸ h 0 x

lemma map_self_dvd_map_neg (x : G) : f x ∣ f (-x) :=
  (dvd_of_eq $ congr_arg f (neg_neg x).symm).trans (map_neg_dvd_map_self h (-x))

lemma map_dvd_map_add_sub_map (x y : G) : f x ∣ f (x + y) - f y :=
  (dvd_of_eq $ congr_arg f (add_sub_cancel x y).symm).trans (h (x + y) y)

def dvd_subgroup (n : ℤ) (h0 : n ∣ f 0) : add_subgroup G :=
  add_subgroup.of_sub {x : G | n ∣ f x} ⟨0, h0⟩ $
  λ x h1 y h2, (dvd_sub_left $ dvd_trans h2 $ map_self_dvd_map_neg h y).mp $
    dvd_trans h1 $ map_dvd_map_add_sub_map h x (-y)

variables (h0 : ∀ x : G, 0 < f x)
include h0

lemma map_neg_eq_map_self (x : G) : f (-x) = f x :=
  int.dvd_antisymm (h0 (-x)).le (h0 x).le
    (map_neg_dvd_map_self h x) (map_self_dvd_map_neg h x)

theorem map_dvd_of_le {x y : G} (h1 : f x ≤ f y) : f x ∣ f y :=
  h1.eq_or_lt.elim dvd_of_eq $ λ h1, let h2 := h y x in
suffices f (y - x) = f x, from dvd_sub_self_right.mp $ (dvd_of_eq this.symm).trans h2,
sub_eq_zero.mp $ int.eq_zero_of_abs_lt_dvd
  (suffices y - x - -x = y, from (dvd_of_eq $ congr_arg f this.symm).trans $
    map_neg_eq_map_self h h0 x ▸ h (y - x) (-x),
  (sub_neg_eq_add _ _).trans (sub_add_cancel y x))
  ((abs_sub_lt_add_of_pos (h0 $ y - x) (h0 x)).trans_le $
    add_le_of_le_sub_right $ int.le_of_dvd (sub_pos_of_lt h1) h2)

end results





/- ### Final solution -/

/-- Final solution, original version -/
alias map_dvd_of_le ← final_solution

end IMO2011N5
end IMOSL
