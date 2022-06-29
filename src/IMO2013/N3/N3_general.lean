import data.set.finite tactic.ring

/-!
# IMO 2013 N3, "Generalized" Version

Let S be a totally ordered set.
Fix a function f : ℕ⁺ → S such that f(ab) = max{f(a), f(b)} for all a, b ∈ ℕ⁺.
Prove that there exists infinitely many positive integers n such that
  f(n⁴ + n² + 1) = f((n + 1)⁴ + (n + 1)² + 1).

## Solution
    
Call n ∈ ℕ⁺ f-good if f(n⁴ + n² + 1) = f((n + 1)⁴ + (n + 1)² + 1), and f-bad otherwise.
Let T(n) = n² + n + 1 for each n ∈ ℕ⁺.
As in the official solution, one notices that, for all n ≥ 2,
  f(T(n²)) = max{f(T(n - 1)), f(T(n))}.
Thus, a positive integer n ≥ 2 is f-good if and only if
  max{f(T(n - 1)), f(T(n))} = max{f(T(n)), f(T(n + 1))}.
Next, we prove the following easy claim.

Claim:
For any f-bad positive integer n, if f(T(n - 1)) ≤ f(T(n)) then f(T(n)) < f(T(n + 1)).

Proof:
If f(T(n + 1)) ≤ f(T(n)), then
  max{f(T(n - 1)), f(T(n))} = max{f(T(n)), f(T(n + 1))} = T(n).
That means n is f-good; a contradiction.
    
Now suppose that there exists finitely many f-good positive integer.
Then there exists N ≥ 2 such that for any n ∈ ℕ⁺ with n ≥ N, n is f-bad.
We divide into two cases:

1. There exists an integer C ≥ N such that f(T(C - 1)) ≤ f(T(C)).

One can show by induction, using the claim, that f(T(k)) > f(T(C)) for any k > C.
In particular f(T(C - 1)) ≤ f(T(C)) < f(T(C²)) = max{f(T(C - 1)), f(T(C))}.
A contradiction.

2. For any n ≥ N, we have f(T(n - 1)) > f(T(n)).

Then one can show by induction that f(T(k)) < f(T(N)) for any k > N.
In particular f(T(N - 1)) < f(T(N)) < f(T(N²)) = max{f(T(N - 1)), f(T(N))}.
This is again a contradiction.

Both cases yield a contradiction.
Thus, there must exist infinitely many good positive integers.

## Notes

1. The generalization could be seen as a cheap generalization.
In the original version, S = ℕ⁺ and f is the largest prime divisor function.
In fact, the problem should be much easier once we notice the property
  f(ab) = max{f(a), f(b)}, which the generalization gives away from the start.
However, one has to work harder to achieve contradiction from the chain of inequalities.

2. The official solution relies on f(T(n)) ≠ f(T(n + 1)) for all n ∈ ℕ⁺, where
f is the largest prime divisor function as in the original problem.
We do not rely on this fact at all.

3. In the implementation, instead of using n in the good predicate, we use n + 1.
-/

namespace IMOSL
namespace IMO2013N3

variables {S : Type*} [linear_order S]

def good (f : ℕ+ → S) (n : ℕ+) := f (n ^ 4 + n ^ 2 + 1) = f ((n + 1) ^ 4 + (n + 1) ^ 2 + 1)



/-- A notation convenience for n² + n + 1. -/
def T (n : ℕ+) := n ^ 2 + n + 1

/-- Equation defining T -/
lemma T_def (n : ℕ+) : T n = n ^ 2 + n + 1 := rfl

/-- Proof of the identity T((n + 1)²) = T(n) T(n + 1). -/
lemma T_sq_factor (n : ℕ+) : T ((n + 1) ^ 2) = T n * T (n + 1) :=
  by unfold T; apply pnat.eq; simp; ring



namespace results

variables {f : ℕ+ → S} (fmax : ∀ a b : ℕ+, f (a * b) = max (f a) (f b))
include fmax

lemma lem1 {n : ℕ+} (h : ¬good f (n + 1)) (h0 : f (T n) ≤ f (T (n + 1))) :
  f (T (n + 1)) < f (T (n + 1 + 1)) :=
begin
  apply lt_of_not_le; intros h1,
  apply h; unfold good,
  change 4 with 2 * 2,
  repeat {rw [pow_mul, ← T_def, T_sq_factor, fmax] },
  rw [max_eq_right h0, max_eq_left h1]
end

lemma lem2 {N : ℕ+} (h : ∀ n : ℕ+, N < n → ¬good f n)
    {C : ℕ+} (h0 : N < C) (h1 : f (T C) ≤ f (T (C + 1))) :
  ∀ k : ℕ+, f (T (C + 1)) < f (T (C + 1 + k)) :=
begin
  suffices : ∀ k : ℕ+, f (T (C + k)) < f (T (C + k + 1)) ∧ f (T (C + 1)) < f (T (C + 1 + k)),
  intros k; rcases this k with ⟨h2, h3⟩; exact h3,
  intros k; induction k using pnat.strong_induction_on with k k_ih,
  rcases decidable.eq_or_ne k 1 with rfl | h2,
  split; exact lem1 fmax (h _ (lt_trans h0 (pnat.lt_add_right C 1))) h1,
  rcases pnat.exists_eq_succ_of_ne_one h2 with ⟨k₀, rfl⟩,
  rcases k_ih k₀ (pnat.lt_add_right k₀ 1) with ⟨h3, h4⟩,
  have h5 : f (T (C + k₀ + 1)) < f (T (C + k₀ + 1 + 1)) :=
    lem1 fmax (h _ (lt_trans h0 (pnat.lt_add_right C (k₀ + 1)))) (le_of_lt h3),
  split,
  rwa ← add_assoc,
  apply lt_trans h4,
  rwa [add_right_comm, add_add_add_comm]
end

lemma lem3 {N : ℕ+} (h : ∀ n : ℕ+, N < n → ¬good f n) {C : ℕ+} (h0 : N < C) :
  f (T (C + 1)) < f (T C) :=
begin
  apply lt_of_not_le; intros h1,
  have h2 := lem2 fmax h h0 h1 (C * (C + 1)),
  rw [← one_add_mul, add_comm 1 C, ← sq, T_sq_factor, fmax, max_eq_right h1] at h2,
  exact lt_irrefl _ h2
end

lemma lem4 {N : ℕ+} (h : ∀ n : ℕ+, N < n → ¬good f n) {C : ℕ+} (h0 : N < C) :
  ∀ k : ℕ+, f (T (C + k)) < f (T C) :=
begin
  intros k,
  apply pnat.rec_on k; clear k,
  exact lem3 fmax h h0,
  intros k h1,
  refine lt_trans _ h1,
  rw ← add_assoc,
  exact lem3 fmax h (lt_trans h0 (pnat.lt_add_right C k))
end
  
end results



/-- Final solution -/
theorem final_solution_general {f : ℕ+ → S} (fmax : ∀ a b : ℕ+, f (a * b) = max (f a) (f b)) :
  set.infinite (set_of (good f)) :=
begin
  apply set.infinite_of_not_bdd_above; rintros ⟨N, h0⟩,
  simp [upper_bounds] at h0,
  have h1 : ∀ n : ℕ+, N < n → ¬good f n :=
  begin
    intros n h1 h2,
    rw lt_iff_not_le at h1,
    exact h1 (h0 h2)
  end,
  have h2 := results.lem4 fmax h1 (pnat.lt_add_right N 1) (N * (N + 1)),
  rw [← one_add_mul, add_comm, ← sq, T_sq_factor, fmax, lt_iff_not_le] at h2,
  exact h2 (le_max_right (f (T N)) (f (T (N + 1))))
end

end IMO2013N3
end IMOSL
