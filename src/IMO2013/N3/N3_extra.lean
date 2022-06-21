import
  data.pnat.basic
  data.nat.basic
  tactic.ring

/-
  Proof of T((n + 1)²) = T(n) T(n + 1), where T(n) = n² + n + 1.
  We also provide the function T for convenience.
  
  We want to use ring tactic to prove the equality.
  Thus, we will use embedding from ℕ⁺ to ℕ.
-/
namespace IMO2013N3

def T (n : ℕ+) := n ^ 2 + n + 1

lemma T_sq_factor :
  ∀ n : ℕ+, T ((n + 1) ^ 2) = T n * T (n + 1) :=
begin
  intros n; unfold T,
  apply pnat.eq,
  simp only [pnat.mul_coe, pnat.one_coe, pnat.pow_coe, pnat.add_coe]; ring,
end

end IMO2013N3
