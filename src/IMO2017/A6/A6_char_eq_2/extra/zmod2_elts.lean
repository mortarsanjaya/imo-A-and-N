import
  data.zmod.basic

namespace IMO2017A6
namespace extra

/-
  This file contains the proof that the elements of zmod 2 are just 0 and 1.
-/
lemma zmod2_elts :
  ∀ c : zmod 2, c = 0 ∨ c = 1 :=
begin
  intros c,
  cases c with x x_prop,
  rcases x with _ | x | x,
  left; refl,
  right; refl,
  rw [nat.succ_lt_succ_iff, nat.add_def, add_zero, nat.succ_lt_succ_iff] at x_prop,
  exfalso; exact nat.not_lt_zero x x_prop,
end

end extra
end IMO2017A6
