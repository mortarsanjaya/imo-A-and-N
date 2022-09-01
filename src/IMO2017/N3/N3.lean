import data.nat.prime algebra.big_operators.basic algebra.periodic

/-! # IMO 2017 N3 -/

namespace IMOSL
namespace IMO2017N3

open function finset

def good (n : ℕ) := ∀ a : ℕ → ℤ, periodic a n → ¬(n : ℤ) ∣ (range n).sum a →
  ∃ i : ℕ, ∀ j : ℕ, 0 < j → j ≤ n → ¬(n : ℤ) ∣ (range j).sum (λ x, a (i + x))





end IMO2017N3
end IMOSL
