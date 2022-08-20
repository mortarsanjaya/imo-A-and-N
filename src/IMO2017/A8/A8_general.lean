import algebra.order.group

/-! # IMO 2017 A8, Generalized Version -/

namespace IMOSL
namespace IMO2017A8

def good {G : Type*} [linear_ordered_add_comm_group G] (f : G → G) :=
  ∀ x y : G, f x < f y → f x ≤ x + y ∧ x + y ≤ f y



section results

variables {G : Type*} [linear_ordered_add_comm_group G]
variables {f : G → G} (fgood : good f) {x y : G} (h : x < y) (h0 : f y < f x)
include fgood h h0

private lemma lem1 {z : G} (h1 : z < f y - y) : f z < f y :=
begin
  rw [lt_sub_iff_add_lt', ← not_le] at h1,
  rw [← not_le, le_iff_lt_or_eq],
  rintros (h2 | h2),
  exact h1 (fgood y z h2).elim_left, 
  rw h2 at h0 h1,
  replace h0 := (fgood z x h0).elim_left,
  refine h1 (le_trans h0 _),
  rw [add_comm, add_le_add_iff_right],
  exact le_of_lt h
end

private lemma lem2 {z : G} (h1 : f x - x < z) : f x < f z :=
begin
  rw [sub_lt_iff_lt_add, ← not_le] at h1,
  rw [← not_le, le_iff_lt_or_eq],
  rintros (h2 | h2),
  exact h1 (fgood z x h2).elim_right, 
  rw ← h2 at h0 h1,
  replace h0 := (fgood y z h0).elim_right,
  refine h1 (le_trans _ h0),
  rw [add_comm, add_le_add_iff_right],
  exact le_of_lt h
end

private lemma lem3 {z : G} (h1 : f y - y < z) (h2 : z < f x - x) : f z = f x ∨ f z = f y :=
begin
  rcases lt_trichotomy (f z) (f y) with h3 | h3 | h3,
  { exfalso,
    refine not_le_of_lt h1 _,
    rw le_sub_iff_add_le,
    exact (fgood z y h3).elim_right },
  { right; exact h3 },
  rcases lt_trichotomy (f x) (f z) with h4 | h4 | h4,
  { exfalso,
    refine not_le_of_lt h2 _,
    rw sub_le_iff_le_add',
    exact (fgood x z h4).elim_left },
  { left; rw h4 },
  { exfalso,
    refine not_lt_of_le (le_trans (fgood y z h3).elim_right (fgood z x h4).elim_left) _,
    rwa [add_comm, add_lt_add_iff_right] }
end

end results



/-- Final solution, General Version -/
theorem final_solution_general {G : Type*} [linear_ordered_add_comm_group G] [densely_ordered G]
  {f : G → G} (fgood : good f) {x y : G} (h : x < y) : f x ≤ f y :=
begin
  rw ← not_lt; intros h0,
  rcases exists_between h with ⟨z, h1, h2⟩,
  obtain (h3 | h3) : f z = f x ∨ f z = f y :=
  begin
    obtain ⟨h3, h4⟩ := fgood y x h0,
    rw ← sub_le_iff_le_add' at h3,
    rw ← le_sub_iff_add_le at h4,
    exact lem3 fgood h h0 (lt_of_le_of_lt h3 h1) (lt_of_lt_of_le h2 h4)
  end,
  { rcases exists_between h1 with ⟨w, h4, h5⟩,
    replace h1 : f z < f (f z - w) := lem2 fgood h2 (by rwa h3) (by rwa sub_lt_sub_iff_left),
    refine not_le_of_lt h1 _,
    obtain (h6 | h6) : f (f x - w) = f x ∨ f (f x - w) = f y :=
      lem3 fgood h h0 (sub_lt_sub h0 (lt_trans h5 h2)) (by rwa sub_lt_sub_iff_left),
    all_goals { rw [h3, h6] },
    exact le_of_lt h0 },
  { rcases exists_between h2 with ⟨w, h4, h5⟩,
    replace h2 : f (f z - w) < f z := lem1 fgood h1 (by rwa h3) (by rwa sub_lt_sub_iff_left),
    refine not_le_of_lt h2 _,
    obtain (h6 | h6) : f (f y - w) = f x ∨ f (f y - w) = f y :=
      lem3 fgood h h0 (by rwa sub_lt_sub_iff_left) (sub_lt_sub h0 (lt_trans h1 h4)),
     all_goals { rw [h3, h6] },
     exact le_of_lt h0 }
end

end IMO2017A8
end IMOSL
