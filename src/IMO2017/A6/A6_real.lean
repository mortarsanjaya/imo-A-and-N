import
  IMO2017.A6.A6_char_ne_2
  data.real.basic

/-
  Solution of 2017 A6 for the originial case : F = ℝ
  This file simply states the main result in "A6_char_ne_2.lean" for the original case.
-/

namespace IMO2017A6

namespace case_real

theorem fn_all :
  set_of (fn_eq ℝ) = {0, 1 - id, id - 1} :=
begin
  apply case_char_ne_2.fn_all ℝ,
  rw ring_char.eq ℝ 0,
  norm_num,
end

end case_real

end IMO2017A6


