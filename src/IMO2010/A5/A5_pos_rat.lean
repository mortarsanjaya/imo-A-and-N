import IMO2010.A5.A5 extra.number_theory.pos_rat_primes

/-! # IMO 2010 A5, `ℚ+` version -/

namespace IMOSL
namespace IMO2010A5

/-- Final solution, original (`ℚ+`) version -/
theorem final_solution_original : ∀ f : {q : ℚ // 0 < q} → {q : ℚ // 0 < q},
  (∀ x y, f (f x ^ 2 * y) = x ^ 3 * f (x * y)) ↔ f = has_inv.inv :=
  final_solution extra.pos_rat_factor_hom.inj

end IMO2010A5
end IMOSL
