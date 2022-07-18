import IMO2013.N3.N3_general data.pnat.prime data.pnat.factors data.finset.lattice

/-! # IMO 2013 N3, Original Version -/

namespace IMOSL
namespace IMO2013N3



namespace extra

/-- The maximum prime divisor of a positive integer n, as a `nat`, or 1 if n = 1. -/
def pnat.max_prime_divisor (n : ℕ+) :=
  (n.factor_multiset : multiset ℕ).fold linear_order.max 1

lemma pnat.max_prime_divisor_one : pnat.max_prime_divisor 1 = 1 :=
  by unfold pnat.max_prime_divisor; rw pnat.factor_multiset_one; refl

lemma pnat.max_prime_divisor_prime (p : ℕ+) (h : p.prime) : pnat.max_prime_divisor p = p :=
begin
  unfold pnat.prime at h,
  unfold pnat.max_prime_divisor,
  let q : nat.primes := ⟨(p : ℕ), h⟩,
  have h0 : p = ↑q := by ext1; rw nat.primes.coe_pnat_nat; refl,
  rw [h0, pnat.factor_multiset_of_prime q, prime_multiset.coe_nat_of_prime,
      multiset.fold_singleton, nat.primes.coe_pnat_nat, subtype.coe_mk],
  exact max_eq_left (le_of_lt (nat.prime.one_lt h))
end

lemma pnat.max_prime_divisor_mul (a b : ℕ+) :
  pnat.max_prime_divisor (a * b) = max (pnat.max_prime_divisor a) (pnat.max_prime_divisor b) :=
begin
  unfold pnat.max_prime_divisor,
  rw [pnat.factor_multiset_mul, ← prime_multiset.coe_coe_nat_monoid_hom,
      add_monoid_hom.map_add, ← multiset.fold_add max, max_self]
end

end extra



/-- Final solution -/
theorem final_solution_original : set.infinite (set_of (good extra.pnat.max_prime_divisor)) :=
  final_solution_general extra.pnat.max_prime_divisor_mul

end IMO2013N3
end IMOSL
