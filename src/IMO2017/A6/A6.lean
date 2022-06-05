import
  algebra.algebra.basic

/-
  IMO 2017 A6 (P2), Generalized Version
  Let F be an arbitrary field.
  Determine all functions f : F → F such that, for all x, y ∈ F,
          f(f(x) f(y)) + f(x + y) = f(xy).
          
  Note:
  1. Case F = ℝ is IMO 2017 A6.
     See file "A6_real.lean".
  2. The case char F ≠ 2 is solved.
     See file "A6_char_ne_2.lean".
  3. The case char F = 2 is still open.
     See file "A6_char_eq_2.lean".
-/

namespace IMO2017A6

universe u
variable F : Type u
variable [field F]

def fn_eq (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y)

end IMO2017A6