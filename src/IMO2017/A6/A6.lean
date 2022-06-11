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
     Solution follow a more general case: char F ≠ 2.

  2. The case char F ≠ 2 is solved.
     See file "A6_char_ne_2.lean".
     For the solution, see https://artofproblemsolving.com/community/c6h1480146p8693244.
     We follow this post by the user "anantmudgal09".
     It happens to work whenever char F ≠ 2.

  3. The case char F = 2 is still open.
     See the folder "A6_char_eq_2".
-/

namespace IMO2017A6

universe u
variable F : Type u
variable [field F]

def fn_eq (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y)

end IMO2017A6