import algebra.order.positive.field number_theory.padics.padic_val data.nat.factorization.basic

/-!
# Correspondence between `ℚ+` and `nat.primes → ℤ`

We construct an explicit homomorphism `(additive) ℚ+ →+ nat.primes → ℤ` and prove injectivity.

TODO:
1. Construct a `finsupp` version and prove bijectivity.
2. See if we can add MUCH more results!
No priority on either as of writing.
-/

namespace IMOSL
namespace extra

def pos_rat_factor_hom : additive {x : ℚ // 0 < x} →+ nat.primes → ℤ :=
{ to_fun := λ q, (λ p, padic_val_rat p q.1),
  map_zero' := funext (λ p, padic_val_rat.one),
  map_add' := λ q r, funext (λ p, by haveI : fact (p : ℕ).prime := ⟨p.2⟩;
    exact padic_val_rat.mul (ne_of_gt q.2) (ne_of_gt r.2)) }

namespace pos_rat_factor_hom

lemma apply (q : {x : ℚ // 0 < x}) (p : nat.primes) :
  pos_rat_factor_hom q p = padic_val_rat p q.1 := rfl

lemma apply' {q : ℚ} (h : 0 < q) (p : nat.primes) :
  pos_rat_factor_hom ⟨q, h⟩ p = padic_val_rat p q := rfl

theorem inj : function.injective pos_rat_factor_hom :=
begin
  ---- Setup
  rw injective_iff_map_eq_zero,
  rintros ⟨q, h⟩ h0,
  suffices : q = 1,
    simp_rw this; refl,
  simp_rw [function.funext_iff, pi.zero_apply, apply] at h0,
  replace h0 : ∀ p : ℕ, p.prime → padic_val_rat p q = 0 := λ p hp, h0 ⟨p, hp⟩,
  
  ---- Now prove that `ν_p(q) = 0` for all `p` prime iff `q = 1`, assuming `q > 0`
  rcases q with ⟨n, d, h1, h2⟩,
  rw ← rat.num_pos_iff_pos at h,
  lift n to ℕ using le_of_lt h; rw nat.cast_pos at h,
  simp_rw [padic_val_rat, sub_eq_zero, nat.cast_inj, padic_val_int.of_nat,
    ← nat.eq_iff_prime_padic_val_nat_eq n d (ne_of_gt h) (ne_of_gt h1)] at h0,
  simp_rw [rat.eq_iff_mul_eq_mul, h0, rat.num_one, rat.denom_one, nat.cast_one],
  exact mul_comm _ 1
end

end pos_rat_factor_hom

end extra
end IMOSL
