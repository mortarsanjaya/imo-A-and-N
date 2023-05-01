import IMO2018.A1.A1 extra.number_theory.pos_rat_primes

/-! # IMO 2018 A1, `ℚ+` version -/

namespace IMOSL
namespace IMO2018A1

def good2 (n : ℤ) {G : Type*} [group G] (f : G → G) :=
  ∀ x y, f ((x * f y) ^ n) = f x ^ n * f y

/-- Final solution, multiplicative version -/
theorem final_solution_multiplicative {n : ℤ} (h : 1 < |n|) {G : Type*} [group G]
  {S : Type*} {ρ : additive G →+ S → ℤ} (h0 : function.injective ρ) :
  ∀ f : G → G, good2 n f ↔ f = 1 :=
  final_solution h h0

/-- Final solution, `ℚ+` version -/
theorem final_solution_rat {n : ℤ} (h : 1 < |n|) :
  ∀ f : {q : ℚ // 0 < q} → {q : ℚ // 0 < q}, good2 n f ↔ f = λ _, 1 :=
  final_solution_multiplicative h extra.pos_rat_factor_hom.inj

end IMO2018A1
end IMOSL
