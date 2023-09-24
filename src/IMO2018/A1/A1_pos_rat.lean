import IMO2018.A1.A1 extra.number_theory.pos_rat_primes

/-! # IMO 2018 A1, `ℚ+` version -/

namespace IMOSL
namespace IMO2018A1

def good' (n : ℤ) {G : Type*} [group G] (f : G → G) :=
  ∀ x y, f ((x * f y) ^ n) = f x ^ n * f y

/-- Final solution, `ℚ+` version -/
theorem final_solution_original {n : ℤ} (h : 1 < |n|)
  {f : {q : ℚ // 0 < q} → {q : ℚ // 0 < q}} :
  good' n f ↔ f = λ _, 1 :=
  final_solution h extra.pos_rat_factor_hom.inj

end IMO2018A1
end IMOSL
