import data.pnat.basic

/-! # IMO 2010 A6 -/

namespace IMOSL
namespace IMO2010A6

section results

variables {f g : ℕ+ → ℕ+} (h : ∀ n : ℕ+, f (g n) = (f n) + 1) (h0 : ∀ n : ℕ+, g (f n) = (g n) + 1)
include h h0

end results



/-- Final solution -/
theorem final_solution {f g : ℕ+ → ℕ+} (h : ∀ n : ℕ+, f (g n) = (f n) + 1)
  (h0 : ∀ n : ℕ+, g (f n) = (g n) + 1) : f = g :=
begin
  sorry
end

end IMO2010A6
end IMOSL
