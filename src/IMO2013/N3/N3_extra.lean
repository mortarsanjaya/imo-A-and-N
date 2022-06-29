import data.pnat.basic data.nat.basic tactic.ring

namespace IMOSL
namespace IMO2013N3

/-- A notation convenience for n² + n + 1. -/
def T (n : ℕ+) := n ^ 2 + n + 1

/-- Equation defining T -/
lemma T_def (n : ℕ+) : T n = n ^ 2 + n + 1 := rfl

/-- Proof of the identity T((n + 1)²) = T(n) T(n + 1). -/
lemma T_sq_factor (n : ℕ+) : T ((n + 1) ^ 2) = T n * T (n + 1) :=
  by unfold T; apply pnat.eq; simp; ring

end IMO2013N3
end IMOSL
