import data.nat.prime data.nat.choose.basic

/-! # IMO 2012 N3 -/

namespace IMOSL
namespace IMO2012N3

def good (m : ℕ) := 2 ≤ m ∧ ∀ n : ℕ, 2 * n ≤ m → m ≤ 3 * n → n ∣ n.choose (m - 2 * n)



end IMO2012N3
end IMOSL
