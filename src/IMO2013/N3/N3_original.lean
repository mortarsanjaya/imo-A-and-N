import IMO2013.N3.N3_general data.pnat.factors

/-! # IMO 2013 N3, Original Version -/

namespace IMOSL
namespace IMO2013N3

open pnat

namespace pnat

/-- The maximum prime divisor of a positive integer n, as a `nat`, or 1 if n = 1. -/
def max_prime_divisor (n : ℕ+) :=
  (n.factor_multiset : multiset ℕ).fold linear_order.max 1

lemma max_prime_divisor_one : max_prime_divisor 1 = 1 :=
  congr_arg (multiset.fold max 1) $ congr_arg coe factor_multiset_one

lemma max_prime_divisor_prime (p : ℕ+) (h : p.prime) : max_prime_divisor p = p :=
  (congr_arg (multiset.fold max 1) (congr_arg coe $ factor_multiset_of_prime ⟨p, h⟩)).trans
    (max_eq_left h.pos)

lemma max_prime_divisor_mul (a b : ℕ+) :
  max_prime_divisor (a * b) = max (max_prime_divisor a) (max_prime_divisor b) :=
  by rw [max_prime_divisor, max_prime_divisor, max_prime_divisor,
    factor_multiset_mul, ← prime_multiset.coe_coe_nat_monoid_hom,
    add_monoid_hom.map_add, ← multiset.fold_add max, max_self]

end pnat



/-- Final solution -/
theorem final_solution_original : set.infinite (set_of (good pnat.max_prime_divisor)) :=
  final_solution_general pnat.max_prime_divisor_mul

end IMO2013N3
end IMOSL
