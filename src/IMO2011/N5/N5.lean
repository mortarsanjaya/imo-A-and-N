import data.int.dvd.basic data.int.order.lemmas algebra.group.defs

/-! # IMO 2011 N5 (P5) -/

namespace IMOSL
namespace IMO2011N5

variables {G : Type*} [add_group G]

def good (f : G → ℤ) := ∀ x y : G, f (x - y) ∣ f x - f y



/-- Given integers `a, b > 0`, we have `|a - b| < a + b` -/
lemma abs_sub_lt_add_of_pos {a b : ℤ} (h : 0 < a) (h0 : 0 < b) : |a - b| < a + b :=
  abs_sub_lt_iff.mpr ⟨(sub_lt_self a h0).trans (lt_add_of_pos_right a h0),
    (sub_lt_self b h).trans (lt_add_of_pos_left b h)⟩





variables {f : G → ℤ} (h : good f)
include h

lemma map_div_map_zero (x : G) : f x ∣ f 0 :=
  dvd_sub_self_left.mp $ (dvd_of_eq $ congr_arg f (sub_zero x).symm).trans (h x 0)

lemma map_neg_dvd_map_self (x : G) : f (-x) ∣ f x :=
  (dvd_sub_right $ map_div_map_zero h (-x)).mp $
    (dvd_of_eq $ congr_arg f (zero_sub x).symm).trans (h 0 x)

variables (h0 : ∀ x : G, 0 < f x)
include h0

lemma map_neg_eq_map_self (x : G) : f (-x) = f x :=
  int.dvd_antisymm (le_of_lt $ h0 (-x)) (le_of_lt $ h0 x) (map_neg_dvd_map_self h x) $
    (dvd_of_eq $ congr_arg f (neg_neg x).symm).trans $ map_neg_dvd_map_self h (-x)

/-- Final solution for the original version -/
theorem final_solution {x y : G} (h1 : f x ≤ f y) : f x ∣ f y :=
  (eq_or_lt_of_le h1).elim dvd_of_eq $ λ h1, let h2 := h y x in
  suffices f (y - x) = f x, by rwa [this, dvd_sub_self_right] at h2,
  sub_eq_zero.mp $ int.eq_zero_of_abs_lt_dvd 
    (by have h3 := h (y - x) (-x);
      rwa [sub_neg_eq_add, sub_add_cancel, map_neg_eq_map_self h h0] at h3)
    ((abs_sub_lt_add_of_pos (h0 $ y - x) (h0 x)).trans_le $
      add_le_of_le_sub_right $ int.le_of_dvd (sub_pos_of_lt h1) h2)

end IMO2011N5
end IMOSL
