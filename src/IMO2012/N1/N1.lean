import
  data.int.basic
  data.int.gcd
  data.set.basic
  ring_theory.int.basic
  tactic.ring

namespace IMO2012N1



/--
  IMO 2012 N1

  A set A of integers is called admissible if it has the following property:
          For any x, y ∈ A and integer k, we have x² + kxy + y² ∈ A.
  Determine all pairs (m, n) of integers such that the only admissible set containing m and n is ℤ.

  Answer: The pair (m, n) satisfies the condition if and only if m and n are coprime.

  See https://www.imo-official.org/problems/IMO2012SL.pdf.
  We will follow the official Solution.
-/
def admissible (A : set ℤ) :=
  ∀ x y : ℤ, x ∈ A → y ∈ A → ∀ k : ℤ, x ^ 2 + k * (x * y) + y ^ 2 ∈ A
def good (m n : ℤ) :=
  ∀ A : set ℤ, admissible A → m ∈ A → n ∈ A → A = set.univ



open set
open int







---- We prove that some pairs are "bad" i.e. not good
namespace bad_pairs

lemma pair_bad1 :
  ∀ c : ℤ, admissible {n : ℤ | c ∣ n} :=
begin
  intros c x y,
  simp only [mem_set_of_eq],
  intros h h0 k,
  cases h with a h,
  cases h0 with b h0,
  rw [h, h0],
  use c * (a * a + k * a * b + b * b),
  ring,
end

theorem pair_bad :
  ∀ m n : ℤ, good m n → is_coprime m n :=
begin
  intros m n h,
  rw ← int.gcd_eq_one_iff_coprime,
  let S := {k : ℤ | ↑(int.gcd m n) ∣ k},
  have h0 : (1 : ℤ) ∈ S,
  { rw h S,
    exact mem_univ 1,
    exact pair_bad1 _,
    all_goals { rw mem_set_of_eq },
    exact int.gcd_dvd_left m n,
    exact int.gcd_dvd_right m n },
  rw mem_set_of_eq at h0,
  apply nat.eq_one_of_dvd_one,
  change (1 : ℕ) with (1 : ℤ).nat_abs,
  exact dvd_nat_abs_of_of_nat_dvd h0,
end

end bad_pairs



---- We prove that the rest are good
namespace good_pairs

lemma pair_good1 :
  ∀ (m : ℤ) (A : set ℤ), admissible A → m ∈ A → ∀ k : ℤ, k * m ^ 2 ∈ A :=
begin
  intros m A h h0 k,
  have h1 := h m m h0 h0 (k - (1 + 1)),
  rwa [← one_mul (m ^ 2), ← sq, ← add_mul, ← add_mul,
       add_comm (1 : ℤ), add_assoc, sub_add_cancel] at h1,
end


lemma pair_good2 :
  ∀ (x y : ℤ) (A : set ℤ), admissible A → x ∈ A → y ∈ A → (x + y) ^ 2 ∈ A :=
begin
  intros x y A h h0 h1,
  rw [add_sq, mul_assoc],
  exact h x y h0 h1 2,
end

lemma pair_good3 :
  ∀ x y : ℤ, is_coprime x y → ∀ A : set ℤ, admissible A → x ∈ A → y ∈ A → (1 : ℤ) ∈ A :=
begin
  intros x y h A h0 h1 h2,
  have h3 : is_coprime (x ^ 2) (y ^ 2) := is_coprime.pow h,
  rcases h3 with ⟨k, m, h3⟩,
  rw [← one_pow 2, ← h3],
  apply pair_good2 _ _ A h0,
  exact pair_good1 x A h0 h1 _,
  exact pair_good1 y A h0 h2 _,
end

theorem pair_good :
  ∀ x y : ℤ, is_coprime x y → good x y :=
begin
  intros x y h A h0 h1 h2,
  rw eq_univ_iff_forall; intros z,
  have h3 := pair_good3 x y h A h0 h1 h2,
  have h4 := pair_good1 (1 : ℤ) A h0 h3 z,
  rwa [one_pow, mul_one] at h4,
end

end good_pairs



---- Wrapper
theorem pair_sol :
  good = is_coprime :=
begin
  apply funext; intros x,
  apply funext; intros y,
  apply propext; split,
  exact bad_pairs.pair_bad x y,
  exact good_pairs.pair_good x y,
end







end IMO2012N1
