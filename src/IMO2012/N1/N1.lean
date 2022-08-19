import ring_theory.int.basic

/-! # IMO 2012 N1 -/

namespace IMOSL
namespace IMO2012N1

open set int

def admissible (A : set ℤ) := ∀ x y : ℤ, x ∈ A → y ∈ A → ∀ k : ℤ, x ^ 2 + k * (x * y) + y ^ 2 ∈ A
def good (m n : ℤ) := ∀ A : set ℤ, admissible A → m ∈ A → n ∈ A → A = set.univ



/-- Characterization of bad pairs -/
private lemma bad_pairs (m n : ℤ) (h : good m n) : is_coprime m n :=
begin
  rw ← int.gcd_eq_one_iff_coprime,
  let c : ℤ := int.gcd m n,
  let S := {k : ℤ | c ∣ k},
  suffices : (1 : ℤ) ∈ S,
    exact nat.eq_one_of_dvd_one (dvd_nat_abs_of_of_nat_dvd this),
  rw h S _ (int.gcd_dvd_left m n) (int.gcd_dvd_right m n),
  exact mem_univ 1,
  intros x y h h0 k,
  rw ← mul_assoc,
  repeat { apply dvd_add },
  exacts [dvd_pow h two_ne_zero, dvd_mul_of_dvd_right h0 _, dvd_pow h0 two_ne_zero]
end

/-- Characterization of good pairs -/
private lemma good_pairs (x y : ℤ) (h : is_coprime x y) : good x y :=
begin
  intros A h0 h1 h2,
  have h3 : ∀ m : ℤ, m ∈ A → ∀ k : ℤ, k * m ^ 2 ∈ A :=
  begin
    intros m h3 k,
    replace h3 := h0 m m h3 h3 (k - (1 + 1)),
    rwa [← sq, ← one_add_mul, add_comm (1 : ℤ), ← add_one_mul, add_assoc, sub_add_cancel] at h3
  end,
  suffices : (1 : ℤ) ∈ A,
  { rw eq_univ_iff_forall; intros z,
    replace h3 := h3 (1 : ℤ) this z,
    rwa [one_pow, mul_one] at h3 },
  obtain ⟨k, m, h4⟩ : is_coprime (x ^ 2) (y ^ 2) := is_coprime.pow h,
  rw [← one_pow 2, ← h4, add_sq, mul_assoc],
  exact h0 _ _ (h3 x h1 _) (h3 y h2 _) 2
end



/-- Final solution -/
theorem final_solution : good = is_coprime :=
  by ext x y; exact iff.intro (bad_pairs x y) (good_pairs x y)

end IMO2012N1
end IMOSL
