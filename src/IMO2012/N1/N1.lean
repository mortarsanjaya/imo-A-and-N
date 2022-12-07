import ring_theory.int.basic

/-! # IMO 2012 N1 -/

namespace IMOSL
namespace IMO2012N1

def admissible (A : set ℤ) := ∀ x y : ℤ, x ∈ A → y ∈ A → ∀ k : ℤ, x ^ 2 + k * x * y + y ^ 2 ∈ A



/-- Final solution -/
theorem final_solution (m n : ℤ) :
  (∀ A : set ℤ, admissible A → m ∈ A → n ∈ A → ∀ x : ℤ, x ∈ A) ↔ is_coprime m n :=
begin
  refine ⟨λ h, _, λ h A h0 h1 h2, _⟩,
  
  ---- If the only admissible set containing `m` and `n` is `ℤ`, then `gcd(m, n) = 1`
  { rw [← int.gcd_eq_one_iff_coprime, ← int.coe_nat_eq_coe_nat_iff, nat.cast_one],
    refine int.eq_one_of_dvd_one (nat.cast_nonneg _)
      (h {k : ℤ | (int.gcd m n : ℤ) ∣ k} _ (int.gcd_dvd_left m n) (int.gcd_dvd_right m n) 1),
    generalize : (int.gcd m n : ℤ) = a,
    clear h m n; intros x y h h0 k,
    refine dvd_add (dvd_add (dvd_pow h two_ne_zero) _) (dvd_pow h0 two_ne_zero),
    exact dvd_mul_of_dvd_right h0 _ },

  ---- If `gcd(m, n) = 1`, then the only admissible set containing `m` and `n` is `ℤ`
  { have h3 : ∀ x : ℤ, x ∈ A → (∀ k : ℤ, k * x ^ 2 ∈ A) :=
      λ x h3 k, by replace h3 := h0 x x h3 h3 (k - (1 + 1));
        rwa [mul_assoc, ← sq, ← one_add_mul, add_comm (1 : ℤ),
             ← add_one_mul, add_assoc, sub_add_cancel] at h3,
    suffices : (1 : ℤ) ∈ A,
      intros x; convert h3 1 this x; rw [one_pow, mul_one],
    replace h : is_coprime (m ^ 2) (n ^ 2) := is_coprime.pow h,
    rcases h with ⟨a, b, h⟩,
    replace h1 := h3 m h1 a,
    replace h2 := h3 n h2 b,
    replace h0 := h0 _ _ h1 h2 2,
    rwa [← add_sq, h, sq] at h0 }
end

end IMO2012N1
end IMOSL
