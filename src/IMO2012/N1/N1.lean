import ring_theory.int.basic

/-!
# IMO 2012 N1

A set A of integers is called admissible if it has the following property:
  for any x, y ∈ A and integer k, we have x² + kxy + y² ∈ A.
Determine all pairs (m, n) of integers such that the only admissible set containing m and n is ℤ.

## Answer

The pair (m, n) satisfies the condition if and only if m and n are coprime.

## Solution

See <https://www.imo-official.org/problems/IMO2012SL.pdf>.
We will follow the official Solution.
-/

open set
open int

namespace IMOSL
namespace IMO2012N1

def admissible (A : set ℤ) := ∀ x y : ℤ, x ∈ A → y ∈ A → ∀ k : ℤ, x ^ 2 + k * (x * y) + y ^ 2 ∈ A
def good (m n : ℤ) := ∀ A : set ℤ, admissible A → m ∈ A → n ∈ A → A = set.univ



namespace results

/-- Characterization of bad pairs -/
lemma bad_pairs :
  ∀ m n : ℤ, good m n → is_coprime m n :=
begin
  intros m n h,
  rw ← int.gcd_eq_one_iff_coprime,
  let c := ↑(int.gcd m n),
  let S := {k : ℤ | c ∣ k},
  have step1 : admissible S :=
  begin
    intros x y h h0 k,
    rw mem_set_of_eq at h h0 ⊢,
    rw ← mul_assoc,
    repeat { apply dvd_add },
    exacts [dvd_pow h two_ne_zero, dvd_mul_of_dvd_right h0 _, dvd_pow h0 two_ne_zero]
  end,
  have step2 : (1 : ℤ) ∈ S,
  { rw h S step1,
    exact mem_univ 1,
    all_goals { rw mem_set_of_eq },
    exact int.gcd_dvd_left m n,
    exact int.gcd_dvd_right m n },
  rw mem_set_of_eq at step2,
  apply nat.eq_one_of_dvd_one,
  change (1 : ℕ) with (1 : ℤ).nat_abs,
  exact dvd_nat_abs_of_of_nat_dvd step2
end

/-- Characterization of good pairs -/
lemma good_pairs (x y : ℤ) (h : is_coprime x y) : good x y :=
begin
  intros A h0 h1 h2,
  have step1 : ∀ m : ℤ, m ∈ A → ∀ k : ℤ, k * m ^ 2 ∈ A :=
  begin
    intros m h3 k,
    have h4 := h0 m m h3 h3 (k - 2),
    ring_nf at h4; exact h4
  end,
  suffices : (1 : ℤ) ∈ A,
  { rw eq_univ_iff_forall; intros z,
    have h3 := step1 (1 : ℤ) this z,
    rwa [one_pow, mul_one] at h3 },
  have h3 : is_coprime (x ^ 2) (y ^ 2) := is_coprime.pow h,
  rcases h3 with ⟨k, m, h3⟩,
  rw [← one_pow 2, ← h3, add_sq, mul_assoc],
  refine h0 _ _ _ _ 2,
  exacts [step1 x h1 _, step1 y h2 _]
end

end results



/-- Final solution -/
theorem final_solution : good = is_coprime :=
begin
  ext x y; split,
  exacts [results.bad_pairs x y, results.good_pairs x y]
end

end IMO2012N1
end IMOSL
