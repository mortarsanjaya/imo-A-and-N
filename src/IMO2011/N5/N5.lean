import data.int.basic algebra.group.defs

/-! # IMO 2011 N5 (P5) -/



namespace IMOSL
namespace IMO2011N5

variables {G : Type*} [add_comm_group G]

def good (f : G → ℤ) := ∀ x y : G, f (x - y) ∣ f x - f y



/-- Final solution for the original version -/
theorem final_solution {f : G → ℤ} (fpos : ∀ x : G, 0 < f x) (h : good f) :
  ∀ x y : G, f x ≤ f y → f x ∣ f y :=
begin
  intros x y h0,
  rw le_iff_eq_or_lt at h0,
  cases h0 with h0 h0,
  rw h0; exact dvd_refl (f y),
  have h1 := h x y,
  suffices : f (x - y) = f x,
    rwa [this, sub_eq_add_neg (f x), dvd_add_self_left, dvd_neg] at h1,
  rw ← sub_eq_zero; apply @int.eq_zero_of_abs_lt_dvd (f y),
  { have h2 := h x (x - y),
    rwa [sub_sub_self, ← neg_sub, dvd_neg] at h2 },
  { rw [← neg_sub (f y), dvd_neg] at h1,
    replace h1 := lt_of_le_of_lt (int.le_of_dvd (sub_pos.mpr h0) h1) (sub_lt_self _ (fpos x)),
    cases le_total 0 (f (x - y) - f x) with h2 h2,
    rw abs_eq_self.mpr h2; exact lt_trans (sub_lt_self _ (fpos x)) h1,
    rw [abs_eq_neg_self.mpr h2, neg_sub]; exact lt_trans (sub_lt_self _ (fpos _)) h0 }
end

end IMO2011N5
end IMOSL
